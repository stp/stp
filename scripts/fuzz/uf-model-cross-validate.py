#!/usr/bin/env python3
"""Cross-validate finite UF models without baking in local solver paths.

STP batch and persistent are always producers; STP batch is always a
validator.  Additional stdin-oriented producers and validators are supplied
as NAME=COMMAND arguments (for example z3, Bitwuzla, and cvc5).  Each SAT
model replaces the corresponding declarations in a replay of the assertion
stack active at that check, and every validator must answer SAT.

Cases are explicit inputs.  The harness rejects reset-driven scripts because
their declaration policy belongs to UFSTP v2's native lifecycle suite rather
than to this branch-neutral model relay.
"""

import argparse
import json
from pathlib import Path
import re
import shlex
import subprocess


VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.MULTILINE)


def strip_comments(text):
    output = []
    index = 0
    quoted = None
    while index < len(text):
        character = text[index]
        if quoted is None:
            if character == ";":
                while index < len(text) and text[index] != "\n":
                    index += 1
                continue
            if character in ("|", '"'):
                quoted = character
            output.append(character)
        else:
            output.append(character)
            if character == quoted:
                quoted = None
        index += 1
    return "".join(output)


def commands(text):
    cleaned = strip_comments(text)
    result = []
    depth = 0
    start = None
    quoted = None
    escaped = False
    for index, character in enumerate(cleaned):
        if quoted == '"':
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                quoted = None
            continue
        if quoted == "|":
            if character == "|":
                quoted = None
            continue
        if character in ('"', "|"):
            quoted = character
            continue
        if character == "(":
            if depth == 0:
                start = index
            depth += 1
        elif character == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced closing parenthesis")
            if depth == 0 and start is not None:
                result.append(cleaned[start:index + 1])
                start = None
    if depth != 0 or quoted is not None:
        raise ValueError("unterminated SMT-LIB command")
    return result


def head(command_text):
    body = command_text[1:].lstrip()
    return body.split(None, 1)[0].rstrip(")") if body else ""


def declared_name(command_text):
    pieces = command_text.split(None, 2)
    if len(pieces) < 2:
        raise ValueError("declaration has no name: %s" % command_text)
    return pieces[1].strip("|")


def subexpressions(block):
    stripped = block.strip()
    if not (stripped.startswith("(") and stripped.endswith(")")):
        return []
    return commands(stripped[1:-1])


def parse_count(command_text):
    match = re.match(r"\([^\s()]+\s+(\d+)\s*\)$", command_text.strip())
    return int(match.group(1)) if match else 1


def parse_case(source):
    if re.search(r"\(reset(?:-assertions)?\b", source):
        raise ValueError("reset/reset-assertions cases are v2-policy-owned")
    levels = [[]]
    checks = []
    producer = ["(set-option :produce-models true)"]
    logic = None
    declarations = []
    macros = []
    for item in commands(source):
        item_head = head(item)
        if item_head == "set-option":
            continue
        if item_head == "set-logic":
            logic = item
        if item_head in ("declare-fun", "declare-const"):
            declarations.append((declared_name(item), item))
        if item_head in ("define-fun", "define-const"):
            macros.append((declared_name(item), item))
        if item_head == "assert":
            levels[-1].append(item)
        elif item_head == "push":
            for _ in range(parse_count(item)):
                levels.append([])
        elif item_head == "pop":
            count = parse_count(item)
            if count >= len(levels):
                raise ValueError("pop exceeds active assertion levels")
            for _ in range(count):
                levels.pop()
        elif item_head in ("check-sat", "check-sat-assuming"):
            assumptions = []
            if item_head == "check-sat-assuming":
                inner = item[item.find("(", 1):item.rfind(")")].strip()
                assumptions = subexpressions(inner)
                if not assumptions and inner:
                    assumptions = [inner]
            checks.append((
                [assertion for level in levels for assertion in level],
                assumptions))
            producer.extend((item, "(get-model)"))
            continue
        elif item_head in ("get-model", "get-value", "exit"):
            continue
        producer.append(item)
    if logic is None or not checks:
        raise ValueError("case needs set-logic and at least one check-sat")
    return {
        "checks": checks,
        "producer": "\n".join(producer) + "\n",
        "logic": logic,
        "declarations": declarations,
        "macros": macros,
    }


def solver_spec(specification):
    if "=" not in specification:
        raise ValueError("solver specification must be NAME=COMMAND")
    name, command_text = specification.split("=", 1)
    argv = shlex.split(command_text)
    if not name or not argv:
        raise ValueError("solver specification must be NAME=COMMAND")
    return name, argv


def invoke(argv, source, timeout):
    process = subprocess.run(
        argv, input=source, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, timeout=timeout, check=False)
    return process.returncode, process.stdout


def balanced_block(lines, start):
    depth = 0
    block = []
    for index in range(start, len(lines)):
        line = lines[index]
        block.append(line)
        depth += line.count("(") - line.count(")")
        if depth == 0:
            return "\n".join(block), index + 1
    return None, start


def verdicts_and_models(output):
    lines = output.splitlines()
    result = []
    index = 0
    while index < len(lines):
        verdict = lines[index].strip()
        if verdict not in ("sat", "unsat", "unknown"):
            index += 1
            continue
        model = None
        next_index = index + 1
        while next_index < len(lines) and not lines[next_index].strip():
            next_index += 1
        if verdict == "sat" and next_index < len(lines) and \
                lines[next_index].lstrip().startswith("("):
            model, next_index = balanced_block(lines, next_index)
        result.append((verdict, model))
        index = max(index + 1, next_index)
    return result


def model_definitions(model):
    if not model:
        return []
    top = subexpressions(model)
    if len(top) == 1 and head(top[0]) == "model":
        top = subexpressions(top[0][top[0].find("model") + 5:].strip())
    return [item for item in top if head(item) == "define-fun"]


def relay_safe(text):
    # Alpha-rename common solver-reserved binder spellings.  These are local
    # names, so the rewrite changes no function interpretation.
    return text.replace("@bzla.", "bzla_").replace("@", "at_")


def replay(case, check_index, definitions):
    defined = {declared_name(item) for item in definitions}
    lines = [case["logic"]]
    lines.extend(relay_safe(item) for item in definitions)
    for name, macro in case["macros"]:
        if name not in defined:
            lines.append(macro)
    for name, declaration in case["declarations"]:
        if name not in defined:
            lines.append(declaration)
    assertions, assumptions = case["checks"][check_index]
    lines.extend(assertions)
    lines.extend("(assert %s)" % assumption for assumption in assumptions)
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stp", required=True)
    parser.add_argument("--case", action="append", required=True)
    parser.add_argument(
        "--producer", action="append", default=[],
        help="additional NAME=COMMAND stdin model producer")
    parser.add_argument(
        "--validator", action="append", default=[],
        help="additional NAME=COMMAND stdin validator")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--evidence-out")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    stp = shlex.split(args.stp)
    if not stp:
        parser.error("--stp must not be empty")
    try:
        extra_producers = [solver_spec(item) for item in args.producer]
        extra_validators = [solver_spec(item) for item in args.validator]
    except ValueError as error:
        parser.error(str(error))
    producers = [
        ("stp-batch", stp + ["--SMTLIB2", "--uninterpreted-functions",
                             "--incremental=off"]),
        ("stp-persistent",
         stp + ["--SMTLIB2", "--uninterpreted-functions",
                "--incremental=on"]),
    ] + extra_producers
    validators = [
        ("stp-batch", stp + ["--SMTLIB2", "--uninterpreted-functions",
                             "--incremental=off"]),
    ] + extra_validators

    failures = []
    checked = 0
    produced = 0
    for case_path_text in args.case:
        case_path = Path(case_path_text)
        try:
            case = parse_case(case_path.read_text())
        except (OSError, ValueError) as error:
            parser.error("%s: %s" % (case_path, error))
        for producer_name, producer_argv in producers:
            returncode, output = invoke(
                producer_argv, case["producer"], args.timeout)
            observations = verdicts_and_models(output)
            if returncode != 0 or len(observations) != len(case["checks"]):
                failures.append({
                    "case": str(case_path), "producer": producer_name,
                    "reason": "producer-command",
                    "returncode": returncode, "output": output[:1000],
                })
                continue
            for check_index, (verdict, model) in enumerate(observations):
                if verdict != "sat":
                    continue
                produced += 1
                definitions = model_definitions(model)
                if not definitions:
                    failures.append({
                        "case": str(case_path), "producer": producer_name,
                        "check": check_index, "reason": "missing-model",
                        "output": output[:1000],
                    })
                    continue
                source = replay(case, check_index, definitions)
                for validator_name, validator_argv in validators:
                    returncode, validation_output = invoke(
                        validator_argv, source, args.timeout)
                    observed = VERDICT.findall(validation_output)
                    checked += 1
                    if returncode == 0 and observed == ["sat"]:
                        continue
                    failures.append({
                        "case": str(case_path), "producer": producer_name,
                        "validator": validator_name, "check": check_index,
                        "reason": "model-rejected", "observed": observed,
                        "returncode": returncode,
                        "output": validation_output[:1000],
                    })

    evidence = {
        "schema": 1,
        "cases": len(args.case),
        "producers": [name for name, _ in producers],
        "validators": [name for name, _ in validators],
        "sat_models_produced": produced,
        "model_validator_pairs": checked,
        "failures": failures,
        "result": "pass" if not failures else "fail",
    }
    encoded = json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    if args.evidence_out:
        Path(args.evidence_out).write_text(encoded)
    print(encoded, end="")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
