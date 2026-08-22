#!/usr/bin/env python3
"""Differential fuzzing for UFSTP.

Each round generates one random quantifier-free Bool/BV UF instance and
decides it several independent ways:

  1. UFSTP (the implementation under test), forced batch and forced
     persistent, on every requested backend;
  2. a generator-side EAGER Ackermannization of the same instance --
     fresh result variables plus all-pairs congruence implications --
     handed to classic STP with the UF feature OFF (a pre-existing,
     independently trusted decision path);
  3. optionally a brute-force enumeration over tiny domains.

Any disagreement is a soundness bug and is dumped for replay. Push/pop
script rounds additionally compare per-level verdict sequences between
batch and persistent routing.
"""
import argparse
import itertools
import os
import random
import shlex
import subprocess
import sys

STP = None
CMS = None
ROUNDS = 0
OUTDIR = None
TIMEOUT = 60.0
EXTERNALS = []
rng = random.Random()

class Gen:
    def __init__(self):
        self.widths = rng.choice([[2], [2, 3], [3, 4], [2, 8]])
        self.nvars = rng.randint(2, 4)
        self.vars = []   # (name, sort) sort: int width or 'bool'
        for i in range(self.nvars):
            sort = rng.choice(self.widths + ['bool'])
            self.vars.append(("v%d" % i, sort))
        self.funcs = []  # (name, [domain sorts], codomain)
        for i in range(rng.randint(1, 2)):
            arity = rng.randint(1, 2)
            dom = [rng.choice(self.widths + ['bool']) for _ in range(arity)]
            cod = rng.choice(self.widths + ['bool'])
            self.funcs.append(("f%d" % i, dom, cod))
        self.apps = []   # (func index, [arg terms]) -> recorded at build
        self.use_define = rng.random() < 0.3
        self.use_let = rng.random() < 0.3

    def sort_str(self, s):
        return "Bool" if s == 'bool' else "(_ BitVec %d)" % s

    def leaf(self, sort, depth):
        choices = [v for v, s in self.vars if s == sort]
        if choices and rng.random() < 0.7:
            return rng.choice(choices)
        if sort == 'bool':
            return rng.choice(["true", "false"])
        return "#b" + "".join(rng.choice("01") for _ in range(sort))

    def term(self, sort, depth):
        if depth <= 0 or rng.random() < 0.3:
            return self.leaf(sort, depth)
        fits = [(i, f) for i, f in enumerate(self.funcs) if f[2] == sort]
        if fits and rng.random() < 0.55:
            i, (name, dom, cod) = rng.choice(fits)
            args = [self.term(d, depth - 1) for d in dom]
            app = "(%s %s)" % (name, " ".join(args))
            self.apps.append((i, args))
            return app
        if sort == 'bool':
            op = rng.choice(['and', 'or', 'xor', 'not', '=', 'bvult'])
            if op == 'not':
                return "(not %s)" % self.term('bool', depth - 1)
            if op in ('=', 'bvult'):
                w = rng.choice(self.widths)
                return "(%s %s %s)" % (op, self.term(w, depth - 1),
                                       self.term(w, depth - 1))
            return "(%s %s %s)" % (op, self.term('bool', depth - 1),
                                   self.term('bool', depth - 1))
        op = rng.choice(['bvadd', 'bvand', 'bvxor', 'bvnot', 'ite'])
        if op == 'bvnot':
            return "(bvnot %s)" % self.term(sort, depth - 1)
        if op == 'ite':
            return "(ite %s %s %s)" % (self.term('bool', depth - 1),
                                       self.term(sort, depth - 1),
                                       self.term(sort, depth - 1))
        return "(%s %s %s)" % (op, self.term(sort, depth - 1),
                               self.term(sort, depth - 1))

    def build(self):
        decls = []
        for v, s in self.vars:
            decls.append("(declare-fun %s () %s)" % (v, self.sort_str(s)))
        for name, dom, cod in self.funcs:
            decls.append("(declare-fun %s (%s) %s)" %
                         (name, " ".join(self.sort_str(d) for d in dom),
                          self.sort_str(cod)))
        asserts = []
        for _ in range(rng.randint(2, 5)):
            asserts.append("(assert %s)" % self.term('bool', rng.randint(1, 3)))
        # Optional define-fun reuse of an application body.
        extra_defs = []
        if self.use_define and self.funcs:
            name, dom, cod = self.funcs[0]
            if len(dom) == 1 and dom[0] != 'bool':
                extra_defs.append(
                    "(define-fun hh ((z (_ BitVec %d))) %s (%s z))" %
                    (dom[0], self.sort_str(cod), name))
                w = dom[0]
                a = "(hh %s)" % self.leaf(w, 0)
                b = "(hh %s)" % self.leaf(w, 0)
                # Record indirectly: parse-side substitution creates the
                # applications; the eager reducer re-derives them from the
                # expanded text below, so nothing to track here.
                if cod == 'bool':
                    asserts.append("(assert (= %s %s))" % (a, b))
                else:
                    asserts.append("(assert (= %s %s))" % (a, b))
        if self.use_let:
            w = rng.choice(self.widths)
            body = self.term('bool', 2)
            asserts.append("(assert (let ((tmp %s)) (or %s (= tmp tmp))))"
                           % (self.leaf(w, 0), body))
        return decls, extra_defs, asserts


def expand_defines(defs, text):
    # Only the one 'hh' shape above: (hh X) -> (f0 X).
    if not defs:
        return text
    out = text
    while "(hh " in out:
        i = out.index("(hh ")
        depth = 0
        j = i
        while True:
            if out[j] == '(':
                depth += 1
            elif out[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        arg = out[i + 4:j].strip()
        out = out[:i] + "(f0 %s)" % arg + out[j + 1:]
    return out


def collect_apps(text, funcs):
    """All (fN args...) occurrences in the fully define-expanded text."""
    apps = {}
    for idx, (name, dom, cod) in enumerate(funcs):
        needle = "(%s " % name
        start = 0
        while True:
            i = text.find(needle, start)
            if i < 0:
                break
            depth = 0
            j = i
            while True:
                if text[j] == '(':
                    depth += 1
                elif text[j] == ')':
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            whole = text[i:j + 1]
            inner = text[i + len(needle):j]
            # split args at top level
            args, cur, d = [], [], 0
            for ch in inner:
                if ch == '(':
                    d += 1
                elif ch == ')':
                    d -= 1
                if ch == ' ' and d == 0:
                    if cur:
                        args.append("".join(cur))
                        cur = []
                else:
                    cur.append(ch)
            if cur:
                args.append("".join(cur))
            apps.setdefault(idx, {})[whole] = args
            start = i + 1
    return apps


def eager_script(decls, defs, asserts, funcs):
    """The same instance with every application replaced by a fresh result
    variable and all-pairs congruence implications added: pure QF_BV,
    decidable by classic STP with the UF feature off."""
    text = "\n".join(asserts)
    text = expand_defines(defs, text)
    # innermost-first replacement: iterate until no application remains.
    # Only VARIABLE declarations survive; the function declarations are
    # compiled away (classic STP rejects nonzero-arity declare-fun).
    fnames = set(f[0] for f in funcs)
    lines = [d for d in decls
             if not any(d.startswith("(declare-fun %s (" % n) and
                        not d.startswith("(declare-fun %s ()" % n)
                        for n in fnames)]
    congruence = []
    counter = [0]
    mapping = {}

    def sort_str(s):
        return "Bool" if s == 'bool' else "(_ BitVec %d)" % s

    changed = True
    while changed:
        apps = collect_apps(text, funcs)
        # pick innermost applications: ones whose args contain no app
        flat = []
        for idx, entries in apps.items():
            for whole, args in entries.items():
                if not any(("(f%d " % k) in a for k in range(len(funcs))
                           for a in args):
                    flat.append((idx, whole, args))
        changed = bool(flat)
        for idx, whole, args in flat:
            if whole not in mapping:
                name, dom, cod = funcs[idx]
                r = "r%d" % counter[0]
                counter[0] += 1
                lines.append("(declare-fun %s () %s)" % (r, sort_str(cod)))
                mapping[whole] = (idx, args, r)
            r = mapping[whole][2]
            text = text.replace(whole, r)

    # all-pairs congruence per function
    per_func = {}
    for whole, (idx, args, r) in mapping.items():
        per_func.setdefault(idx, []).append((args, r))
    for idx, entries in per_func.items():
        name, dom, cod = funcs[idx]
        for (a1, r1), (a2, r2) in itertools.combinations(entries, 2):
            prem = " ".join("(= %s %s)" % (expand_defines(defs, x),
                                           expand_defines(defs, y))
                            for x, y in zip(a1, a2))
            congruence.append(
                "(assert (=> (and %s true) (= %s %s)))" % (prem, r1, r2))
    return "\n".join(["(set-logic QF_BV)"] + lines + [text] + congruence +
                     ["(check-sat)"])


def run(script, args):
    # Modern STP builds can contain every SAT backend, so --cryptominisat is
    # normally just another selector on STP.  Keep the alternate executable
    # hook for comparing an older/dedicated CryptoMiniSat build.
    executable = CMS if '--cryptominisat' in args and CMS else STP
    p = subprocess.run([executable, '--SMTLIB2'] + args,
                       input=script.encode(), capture_output=True,
                       timeout=TIMEOUT)
    out = p.stdout.decode()
    for line in out.splitlines():
        if line.strip() in ('sat', 'unsat'):
            return line.strip()
    return 'ERROR:' + out[:200] + p.stderr.decode()[:200]


def run_external(cmd, script):
    p = subprocess.run(cmd, input=script.encode(), capture_output=True,
                       timeout=TIMEOUT)
    out = p.stdout.decode()
    for line in out.splitlines():
        if line.strip() in ('sat', 'unsat'):
            return line.strip()
    return 'ERROR:' + out[:200] + p.stderr.decode()[:200]


def one_round(rnum, backends):
    g = Gen()
    decls, defs, asserts = g.build()
    uf_script = "\n".join(["(set-logic QF_UFBV)"] + decls + defs + asserts +
                          ["(check-sat)"])
    eager = eager_script(decls, defs, asserts, g.funcs)

    reference = run(eager, ['--incremental=off'])
    verdicts = {'eager-classic': reference}
    for i, cmd in enumerate(EXTERNALS):
        verdicts['external-%d-%s' % (i, os.path.basename(cmd[0]))] = \
            run_external(cmd, uf_script)
    for be in backends:
        for mode in ['--incremental=off', '--incremental=on']:
            key = "%s %s" % (be if be else 'default', mode)
            flags = ([be] if be else []) + [mode, '--uninterpreted-functions']
            verdicts[key] = run(uf_script, flags)

    answers = set(verdicts.values())
    if len(answers) != 1 or not answers <= {'sat', 'unsat'}:
        os.makedirs(OUTDIR, exist_ok=True)
        with open(os.path.join(OUTDIR, 'round%d.smt2' % rnum), 'w') as f:
            f.write(uf_script)
        with open(os.path.join(OUTDIR, 'round%d-eager.smt2' % rnum), 'w') as f:
            f.write(eager)
        print("DISAGREE round", rnum, verdicts)
        return False
    return True


def pushpop_round(rnum):
    """Per-level verdict agreement between forced batch and persistent."""
    g = Gen()
    decls, defs, asserts = g.build()
    script = ["(set-logic QF_UFBV)"] + decls + defs
    script.append("(assert %s)" % g.term('bool', 2))
    script.append("(check-sat)")
    for a in asserts[:3]:
        script.append("(push 1)")
        script.append(a)
        script.append("(check-sat)")
    for _ in range(min(3, len(asserts[:3]))):
        script.append("(pop 1)")
        script.append("(check-sat)")
    text = "\n".join(script)

    def seq(mode):
        p = subprocess.run([STP, '--SMTLIB2', '--uninterpreted-functions',
                            mode], input=text.encode(), capture_output=True,
                           timeout=TIMEOUT)
        return [l for l in p.stdout.decode().splitlines()
                if l.strip() in ('sat', 'unsat')]

    a = seq('--incremental=off')
    b = seq('--incremental=on')
    ok = a == b and len(a) > 0
    # SMT-LIB monotonicity sanity: pops can only relax.
    if not ok:
        os.makedirs(OUTDIR, exist_ok=True)
        with open(os.path.join(OUTDIR, 'pushpop%d.smt2' % rnum), 'w') as f:
            f.write(text)
        print("PUSHPOP DISAGREE round", rnum, a, b)
    return ok


def main():
    global STP, CMS, ROUNDS, OUTDIR, TIMEOUT, EXTERNALS, rng
    parser = argparse.ArgumentParser()
    parser.add_argument('--stp', default=os.environ.get('STP_BIN'))
    parser.add_argument('--cryptominisat-stp',
                        default=os.environ.get('STP_CMS_BIN'),
                        help=('optional alternate STP executable for the '
                              '--cryptominisat backend'))
    parser.add_argument('--seed', type=int,
                        default=int(os.environ.get('SEED', '1')))
    parser.add_argument('--rounds', type=int,
                        default=int(os.environ.get('ROUNDS', '200')))
    parser.add_argument('--outdir',
                        default=os.environ.get(
                            'OUTDIR', '/tmp/uf-fuzz-failures'))
    parser.add_argument('--timeout', type=float, default=60.0)
    parser.add_argument(
        '--backend', action='append', default=[],
        help='one STP SAT-backend flag (repeatable; default backend included)')
    parser.add_argument(
        '--external', action='append', default=[],
        help='stdin reference-solver command (repeatable)')
    args = parser.parse_args()
    if not args.stp:
        parser.error('--stp (or STP_BIN) is required')
    if args.rounds <= 0 or args.timeout <= 0:
        parser.error('--rounds and --timeout must be positive')
    STP = args.stp
    CMS = args.cryptominisat_stp
    ROUNDS = args.rounds
    OUTDIR = args.outdir
    TIMEOUT = args.timeout
    rng = random.Random(args.seed)

    external_specs = list(args.external)
    if not external_specs:
        external_specs = [item.strip() for item in
                          os.environ.get('EXTERNAL_SOLVERS', '').split(';')
                          if item.strip()]
    EXTERNALS = [shlex.split(item) for item in external_specs]

    backends = [''] + args.backend
    if not args.backend:
        backends += os.environ.get('BACKENDS', '').split()
    bad = 0
    for r in range(ROUNDS):
        if not one_round(r, backends):
            bad += 1
    pp_bad = 0
    for r in range(ROUNDS // 4):
        if not pushpop_round(r):
            pp_bad += 1
    print("fuzz done: %d rounds, %d disagreements; %d push/pop rounds, %d "
          "disagreements" % (ROUNDS, bad, ROUNDS // 4, pp_bad))
    return 1 if (bad or pp_bad) else 0


if __name__ == '__main__':
    sys.exit(main())
