#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (c) 2013 Mate Soos

# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

from __future__ import with_statement  # Required in 2.5
from __future__ import print_function
import subprocess
import os
import re
import commands
import resource
import time
import struct
import random
import optparse

maxTime = 200
maxTimeDiff = 20


class PlainHelpFormatter(optparse.IndentedHelpFormatter):
    def format_description(self, description):
        if description:
            return description + "\n"
        else:
            return ""

usage = "usage: %prog [options] --fuzz"
desc = """Example usages:

* fuzz the solver with fuzz-generator
   ./fuzz_test.py -f
"""

parser = optparse.OptionParser(usage=usage, description=desc, formatter=PlainHelpFormatter())
parser.add_option("--exec", metavar="SOLVER", dest="solver",
                  default="../../build/stp",
                  help="STP executable. Default: %default")
parser.add_option("--check", metavar="CHECKER", dest="checker",
                  default="boolector",
                  help="Boolector executable. Default: %default")

parser.add_option("--verbose", "-v", action="store_true",
                  default=False, dest="verbose",
                  help="Print more output")

parser.add_option("--extraopts", "-e", metavar="OPTS", dest="extra_options",
                  default="",
                  help="Extra options to give to STP")

parser.add_option("-n", "--num", dest="num_todo", type=int,
                  help="How many fuzzings to do")

parser.add_option("--novalgrind", dest="novalgrind", default=False,
                  action="store_true", help="No valgrind installed")

(options, args) = parser.parse_args()


def setlimits():
    resource.setrlimit(resource.RLIMIT_CPU, (maxTime, maxTime))


def unique_fuzz_file(file_name_begin):
    counter = 1
    while 1:
        file_name = file_name_begin + '_' + str(counter) + ".smt2"
        try:
            fd = os.open(file_name, os.O_CREAT | os.O_EXCL)
            os.fdopen(fd).close()
            return file_name
        except OSError:
            pass
        counter += 1


class Tester:

    def __init__(self):
        self.cryptominisat4_available = self.check_cryptominisat4()

    def random_options(self):
        cmd = " "
        # opts = ["--disable-simplifications", "-w", "-a", "--disable-cbitp"
        # , "--disable-equality", "-r", "--oldstyle-refinement"]

        # print options
        # --print-back-CVC", "--print-back-SMTLIB2"
        # --print-back-SMTLIB1", "--print-back-GDL", "--print-back-dot"
        # -p (COUNTEREXAMPLE), -s (STATS), -t (quick stats), -v (notes), -y (counterexample in binary)
        # -b (print back input to output)

        # input options
        # , "--SMTLIB1", "-m", "--SMTLIB2"

        # output options
        # --output-CNF --output-bench --exit-after-CNF
        opts = ["--disable-simplifications", "-w", "-a", "--disable-cbitp",
                "--disable-equality",
                "-r"]

        for opt in opts:
            if random.randint(0, 1) == 0:
                cmd += opt + " "

        choose_solver = ["", "--simplifying-minisat", "--minisat"]
        if self.cryptominisat4_available:
            choose_solver.append("--cryptominisat4")

        cmd += " %s " % random.choice(choose_solver)
        if self.cryptominisat4_available:
            cmd += " --threads %d " % random.choice([1, 4, 10])

        #if random.randint(0,1) == 1 :
        #    cmd += "-i %d " % random.randint(0,1000)

        return cmd

    def _check_solver_exists(self):
        if os.path.isfile(options.solver) is not True:
            print("Error: Cannot find STP executable. Searched in: '%s'" % options.solver)
            print("Error code 300")
            exit(300)

    def execute(self, fname, needToLimitTime=False):
        self._check_solver_exists()

        # construct command
        command = ""
        if not options.novalgrind and random.randint(0, 10) == 0:
            command += "valgrind -q --leak-check=full --track-origins=yes  --error-exitcode=173 "

        command += options.solver
        command += self.random_options()
        command += "-p "  # yes, print counterexample

        command += options.extra_options + " "
        command += fname
        print("Executing: %s " % command)

        # print time limit
        if options.verbose:
            print("CPU limit of parent (pid %d)" % os.getpid(), resource.getrlimit(resource.RLIMIT_CPU))

        # if need time limit, then limit
        if needToLimitTime:
            p = subprocess.Popen(command.rsplit(), stdout=subprocess.PIPE, preexec_fn=setlimits)
        else:
            p = subprocess.Popen(command.rsplit(), stdout=subprocess.PIPE)

        # print time limit after child startup
        if options.verbose:
            print("CPU limit of parent (pid %d) after startup of child" %
                  (os.getpid(), resource.getrlimit(resource.RLIMIT_CPU)))

        # Get solver output
        consoleOutput, err = p.communicate()
        if options.verbose:
            print("CPU limit of parent (pid %d) after child finished executing" %
                  (os.getpid(), resource.getrlimit(resource.RLIMIT_CPU)))

        if p.returncode == 173:
            print("Valgrind is indicating an error!")
            print(err)
            print(consoleOutput)
            exit(-1)

        return consoleOutput

    def parse_solution_from_output(self, output_lines):
        if len(output_lines) == 0:
            print("Error! SMT solver output is empty!")
            print("output lines: ", output_lines)
            print("Error code 500")
            exit(500)

        # solution will be put here
        satunsatfound = False
        vlinefound = False
        value = {}

        # parse in solution
        for line in output_lines:
            # skip comment
            if (re.match('^c ', line)):
                continue

            # solution
            if (re.match('^sat', line)):
                unsat = False
                satunsatfound = True
                continue

            if (re.match('^unsat', line)):
                unsat = True
                satunsatfound = True
                continue

            # parse in solution
            if (re.match('^ASSERT', line)):
                vlinefound = True
                print(line)
                # ignoring this

        if satunsatfound == False:
            print("Error: Cannot find line 'sat/unsat' in output!")
            print(output_lines)
            print("Error code 500")
            exit(500)

        return (unsat, value)

    def checkUNSAT(self, fname):
        # execute with the other solver
        toexec = "%s %s" % (options.checker, fname)
        print("Solving with other solver.. '%s'" % toexec)
        currTime = time.time()
        p = subprocess.Popen(toexec.rsplit(), stdout=subprocess.PIPE,
                             preexec_fn=setlimits)
        consoleOutput2 = p.communicate()[0]

        # if other solver was out of time, then we can't say anything
        diffTime = time.time() - currTime
        if diffTime > maxTime-maxTimeDiff:
            print("Other solver: too much time to solve, aborted!")
            return None

        # extract output from the other solver
        print("Checking other solver output...")
        (otherSolverUNSAT, otherSolverValue) = self.parse_solution_from_output(consoleOutput2.split("\n"))

        # check if the other solver agrees with us
        return otherSolverUNSAT

    def check_cryptominisat4(self):
        command = options.solver
        command += " -h"
        p = subprocess.Popen(command.rsplit(), stdout=subprocess.PIPE, preexec_fn=setlimits)
        consoleOutput, _ = p.communicate()
        for line in consoleOutput.split("\n"):
            if "cryptominisat4" in line:
                return True
        return False

    def check(self, fname, fnameSolution=None, needSolve=True, needToLimitTime=False):
        currTime = time.time()

        # Do we need to solve the problem, or is it already solved?
        if needSolve:
            consoleOutput = self.execute(fname, needToLimitTime)
        else:
            if not os.path.isfile(fnameSolution):
                print("ERROR! Solution file '%s' is not a file!" % fnameSolution)
                exit(-1)
            f = open(fnameSolution, "r")
            consoleOutput = f.read()
            f.close()
            print("Read solution from file ", fnameSolution)

        # if time was limited, we need to know if we were over the time limit
        # and that is why there is no solution
        if needToLimitTime:
            diffTime = time.time() - currTime
            if diffTime > maxTime - maxTimeDiff:
                print("Too much time to solve, aborted!")
                return
            else:
                print("Within time limit: %f s" % (time.time() - currTime))

        print("filename: %s" % fname)
        print("Checking console output...")
        (unsat, value) = self.parse_solution_from_output(consoleOutput.split("\n"))
        otherSolverUNSAT = True

        if not unsat:
            print("TODO: must test solution is correct SAT!")
            #self.test_found_solution(value, fname)

            ret = self.checkUNSAT(fname)
            if ret is None:
                print("Other solver time-outed, cannot check")
            elif ret is False:
                print("SAT verified by other solver")
            else:
                print("Grave bug: UNSAT-> SAT : Other solver didn't find a solution!!")
                exit()
            return

        # it's UNSAT and we should not check, so exit
        if self.check_unsat is False:
            print("Cannot check -- output is UNSAT")
            return

        # check with other solver
        ret = self.checkUNSAT(fname)
        if ret is None:
            print("Other solver time-outed, cannot check")
        elif ret is True:
            print("UNSAT verified by other solver")
        else:
            print("Grave bug: SAT-> UNSAT : Other solver found solution!!")
            exit()

    def callFromFuzzer(self, base_dir, fuzzer, file_name):
        seed = struct.unpack("<L", os.urandom(4))[0]
        seed %= 10000000
        call = "sh -c \"cd {0}/{1} && {2} -seed {5} > {3}/{4}\""
        call = call.format(base_dir, fuzzer[0], fuzzer[1], os.getcwd(),
                           file_name, seed)
        return call

    def fuzz_test(self):
        fuzzers = [["fuzzsmt", "./fuzzsmt QF_ABV"]]

        directory = "../../../"
        for fuzzer in fuzzers:
            file_name = unique_fuzz_file("fuzzTest")

            # create the fuzz file
            call = self.callFromFuzzer(directory, fuzzer, file_name)
            print("calling ", fuzzer, " : ", call)
            out = commands.getstatusoutput(call)

            # check file
            self.check(fname=file_name, needToLimitTime=True)

            # remove temporary filenames
            os.unlink(file_name)

tester = Tester()


tester.check_unsat = True
if options.num_todo:
    for _ in xrange(options.num_todo):
        tester.fuzz_test()

else:
    while(True):
        tester.fuzz_test()

exit(0)
