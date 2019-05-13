#!/usr/bin/python

import os
import shutil
import subprocess
import sys

# Norbert Manthey, 2019
#
# This script runs several SAT solvers simultaneously for a given number of
# cores and an input formula
#
# Example:
#   ./multi-solver.py 1 input.cnf tmpDirectory # run sequential solver
#   ./multi-solver.py 4 input.cnf tmpDirectory # run parallel solvers for 4 cores


# Setup solvers
def setup_solvers(threads):
    solvers = {}

    # Call strings for solvers
    cmsString = "cryptominisat5 --verb 0 --printsol 0 --threads "  # $(nproc)"
    rissString = "riss -verb=0 -quiet "
    minisatString = "minisat -verb=0 "

    # Set threads
    cmsThreads = 1
    if threads > 3:
        cmsThreads = threads - 3

    dir_path = os.path.dirname(os.path.realpath(__file__))
    dir_path = os.path.join(dir_path, "")

    solvers["cms"] = dir_path+cmsString + str(cmsThreads) + " "
    if threads > 1:
        solvers["riss"] = dir_path+rissString
    if threads > 2:
        solvers["minisat"] = dir_path+minisatString

    return solvers

# Print header
print("c multi-solver")
print("c Norbert Manthey, 2019")

# Handle parameters
if(len(sys.argv) < 3):
    print("c usage: ./multi-solver.py cores input.cnf [tmpDirectory]")
    sys.exit(0)
threads = int(sys.argv[1])
inputFile = sys.argv[2]

# Setup tmp files
tmpDir = "/tmp"
if(len(sys.argv) > 3):
    tmpDir = sys.argv[3]
tmpFile = tmpDir + "/multi-solver" + str(os.getpid())
# Let user know that everything has been read correctly
print("c solve {} with tmp files {}".format(inputFile, tmpFile))

# Start the solvers, each in its private process group
pids = set()
pids = {}
runningPids = []
solvers = setup_solvers(threads)

# Start solvers step by step
for key in solvers.keys():
    solver = key
    callString = solvers[key] + inputFile
    try:
        solverProcess = subprocess.Popen(callString.split(), stdout=open(tmpFile + "." + solver + ".out", "w"),
                                         stderr=open(tmpFile + "." + solver + ".err", "w"), preexec_fn=os.setpgrp)
        pids[solver] = solverProcess.pid
        runningPids.append(solverProcess.pid)
        print("c started {} with pid {}".format(solver, solverProcess.pid))
    except Exception as e:
        print("c starting {} via {} failed with exception {}".format(solver, callString, e))


# Wait until the first solver returns
winner = ""
winnerCode = 0
runningSolvers = 3
while runningPids:
    pid, retval = os.wait()
    runningPids.remove(pid)
    print("c finished {} with return value {}".format(pid, str(retval)))
    runningSolvers -= 1
    # extract the exit code
    sig = retval & 255
    exitCode = (retval >> 8) & 255
    print("c signal: {} exit code: {}".format(sig, exitCode))
    # If the exit code is nice, select the winner
    if sig == 0 and (exitCode == 10 or exitCode == 20):
        winnerCode = exitCode  # store exit code
        for solver in pids.keys():
            if pid == pids[solver]:
                winner = solver
            # Do not wait for the other process as well
            # in case a solution has been found
            break

# Output the result
if winnerCode != 0:
    print("c winner: {}".format(winner))

    f = open(tmpFile + "." + winner + ".out", "r")
    if f:
        shutil.copyfileobj(f, sys.stdout)
else:
    print("s UNKNOWN")


# Kill the other process, and its child processes
for p in runningPids:
    os.kill(-p, 15)

# Clean up the temporary files
for solver in solvers.keys():
    os.unlink(tmpFile + "."+solver+".err")
    os.unlink(tmpFile + "."+solver+".out")

# Exit with the correct exit code
sys.exit(winnerCode)
