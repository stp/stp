This page describes the output format that STP uses when passed the
``--output-cnf`` option. For example:

::

    c Result of efficient AIG-to-CNF conversion using package CNF
    p cnf 7 8
    2 3 -4 6 0
    2 4 -5 6 0
    2 -4 5 6 0
    -2 -6 0
    -2 4 5 0
    -2 -3 -4 -5 0
    7 0
    2 0

Lines beginning with ``c`` are comment lines, which are disregarded.

The line beginning with ``p`` is the problem line, which is of the
format ``p cnf nvars nclauses`` where *nvars* and *nclauses* are the
number of variables and clauses, respectively.

Each other line encodes one clause. Clauses are defined as a list of
literals followed by a ``0``. Positive literals are 1, 2, …, and
negative literals are -1, -2, ….

The code that generates the output file is in
extlib-abc/aig/cnf/cnfMan.c.
