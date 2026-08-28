Architecture
============

STP is an efficient decision procedure for the validity (or
satisfiability) of formulas from a quantifier-free many-sorted theory of
fixed-width bitvectors, one-dimensional arrays and IEEE-754
floating-point. The functions in STP’s input language include
concatenation, extraction, left/right shift, sign-extension, unary minus,
addition, multiplication, (signed) modulo/division, bitwise Boolean
operations, if-then-else terms, and array reads and writes. The
floating-point functions cover the four arithmetic operations and the
fused multiply-add, square root, remainder, absolute value, negation,
rounding to integral, minimum and maximum, and the conversions to and
from bitvectors, each under any of the five rounding modes. The
predicates in the language include equality and (signed) comparators
between bitvector terms, and the ordering comparisons and the
classifications over floating-point terms.

The basic architecture of STP essentially follows the idea of word-level
preprocessing followed by translation to SAT (a query with no solver
flag goes to the first backend the build compiled in, preferring
CryptoMiniSat, then CaDiCaL, then Riss, then MiniSat; ``--cadical``,
``--cryptominisat`` and ``--minisat`` select a compiled-in backend at run
time). In particular, we
introduce several new heuristics for the preprocessing step, including
abstraction-refinement in the context of arrays, a new bitvector linear
arithmetic equation solver, and some
interesting simplifications. These heuristics help us achieve several
orders of magnitude of performance improvement over earlier tools, and over
straight-forward translation to SAT. STP has been heavily tested on
thousands of examples sourced from various real-world applications such
as program analysis and bug-finding tools like EXE, and equivalence
checking tools and theorem-provers.

The solving pipeline
--------------------

This is the batch pipeline, which runs for every ``check-sat`` that the
incremental driver does not take. Dashed boxes are stages that only some
queries reach; the brackets on the right mark the three places the
pipeline repeats itself.

.. raw:: html

   <style>
   .pipe-fig { margin: 1.6em 0 0.3em; }
   .pipe-fig svg { max-width: 100%; height: auto; display: block; margin: 0 auto;
                   font-family: 'Vollkorn', Georgia, serif; }
   .pipe-fig a { text-decoration: none; cursor: pointer; }
   .pipe-fig a rect { transition: fill .12s ease-in-out; }
   .pipe-fig a:hover rect { fill: #EFECD8; }
   .pipe-fig a:focus { outline: none; }
   .pipe-fig a:focus rect { stroke: #3F6B63; stroke-width: 2.4; }
   .pipe-hint { text-align: center; font-size: .9em; color: #8C8879;
                margin: 0 0 1.8em; }
   .pipe-detail { border-left: 3px solid transparent; padding: .25em 0 .25em 1em;
                  margin: 0 0 1em; scroll-margin-top: 1em; }
   .pipe-detail > h4 { margin: 0 0 .25em; font-size: 1.05em; }
   .pipe-detail > p { margin: 0; }
   .pipe-detail:target { border-left-color: #3F6B63; background: #EDF2EF; }
   .pipe-detail:target > h4 { color: #3F6B63; }
   </style>
   <div class="pipe-fig">
   <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 600 1093" role="img" aria-labelledby="pipe-t pipe-d">
   <title id="pipe-t">STP's solving pipeline</title>
   <desc id="pipe-d">The stages a query passes through, from parsing to the SAT solver. Each box links to a summary of that stage below the diagram. Constant bit propagation runs three times: once before the size-reducing passes, once after the simplification loop, and once more to feed its fixed bits to the bit-blaster. Three stages repeat until they reach a fixed point: the size-reducing passes, the simplify-and-solve loop, and array refinement around the SAT solver.</desc>
   <defs><marker id="ah" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0 0 L8 4 L0 8 z" fill="#C9C3A4"/></marker><marker id="ahl" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0 L8 4 L0 8 z" fill="#3F6B63"/></marker></defs>
   <line x1="208" y1="74" x2="208" y2="87" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="149" x2="208" y2="162" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="224" x2="208" y2="237" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="299" x2="208" y2="312" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="374" x2="208" y2="387" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="464" x2="208" y2="477" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="539" x2="208" y2="552" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="599" x2="208" y2="612" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="659" x2="208" y2="672" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="734" x2="208" y2="747" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="809" x2="208" y2="822" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="884" x2="208" y2="897" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="959" x2="208" y2="972" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <line x1="208" y1="1019" x2="208" y2="1032" stroke="#C9C3A4" stroke-width="1.4" marker-end="url(#ah)"/>
   <a href="#stage-input">
   <title>SMT-LIB2 input — click for a summary</title>
   <rect x="6" y="14" width="404" height="60" rx="7" fill="#E7E2C6" stroke="#C9C3A4" stroke-width="1.4"/>
   <text x="22" y="34" font-size="14.5" fill="#46433A" font-weight="600">SMT-LIB2 input</text>
   <text x="22" y="51" font-size="11.5" fill="#8C8879">parsed into a hash-consed multigraph; SimplifyingNodeFactory</text>
   <text x="22" y="66" font-size="11.5" fill="#8C8879">rewrites each node as it is built</text>
   </a>
   <a href="#stage-fp-prepare">
   <title>Floating-point preparation — click for a summary</title>
   <rect x="6" y="89" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1" stroke-dasharray="5 3"/>
   <text x="22" y="109" font-size="14.5" fill="#46433A" font-weight="600">Floating-point preparation</text>
   <text x="22" y="126" font-size="11.5" fill="#8C8879">only with a floating-point theory — makes the partial operations</text>
   <text x="22" y="141" font-size="11.5" fill="#8C8879">total and pins every rounding mode to a legal encoding</text>
   </a>
   <a href="#stage-array-equality">
   <title>Array-equality lowering — click for a summary</title>
   <rect x="6" y="164" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1" stroke-dasharray="5 3"/>
   <text x="22" y="184" font-size="14.5" fill="#46433A" font-weight="600">Array-equality lowering</text>
   <text x="22" y="201" font-size="11.5" fill="#8C8879">only with --array-equality — abstracts each whole-array equality</text>
   <text x="22" y="216" font-size="11.5" fill="#8C8879">to a Boolean and conjoins its witness constraints</text>
   </a>
   <a href="#stage-ackermann">
   <title>Eager Ackermannisation — click for a summary</title>
   <rect x="6" y="239" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1" stroke-dasharray="5 3"/>
   <text x="22" y="259" font-size="14.5" fill="#46433A" font-weight="600">Eager Ackermannisation</text>
   <text x="22" y="276" font-size="11.5" fill="#8C8879">only under 10 array reads — rewrites them away outright, so the</text>
   <text x="22" y="291" font-size="11.5" fill="#8C8879">bit-vector passes below see no arrays</text>
   </a>
   <a href="#stage-cbp-1">
   <title>Constant bit propagation — click for a summary</title>
   <rect x="6" y="314" width="404" height="60" rx="7" fill="#DFE8E3" stroke="#9CBAB1" stroke-width="1.5"/>
   <text x="22" y="334" font-size="14.5" fill="#3F6B63" font-weight="600">Constant bit propagation</text>
   <text x="394" y="334" font-size="10.5" fill="#3F6B63" text-anchor="end" font-style="italic">reaches a fixed point</text>
   <text x="22" y="351" font-size="11.5" fill="#8C8879">propagates a worklist to its own fixed point, downwards and up;</text>
   <text x="22" y="366" font-size="11.5" fill="#8C8879">fully fixed nodes become constants</text>
   </a>
   <a href="#stage-size-reducing">
   <title>Size-reducing passes — click for a summary</title>
   <rect x="6" y="389" width="404" height="75" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1"/>
   <text x="22" y="409" font-size="14.5" fill="#46433A" font-weight="600">Size-reducing passes</text>
   <text x="22" y="426" font-size="11.5" fill="#8C8879">equality propagation · unconstrained elimination · strength</text>
   <text x="22" y="441" font-size="11.5" fill="#8C8879">reduction · pure literals · split extracts · merge same ·</text>
   <text x="22" y="456" font-size="11.5" fill="#8C8879">flatten · sharing-aware rewriting · linear bit-vector solve</text>
   </a>
   <a href="#stage-fp-lower">
   <title>Floating-point lowering — click for a summary</title>
   <rect x="6" y="479" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1" stroke-dasharray="5 3"/>
   <text x="22" y="499" font-size="14.5" fill="#46433A" font-weight="600">Floating-point lowering</text>
   <text x="22" y="516" font-size="11.5" fill="#8C8879">only with a floating-point theory — float operations become</text>
   <text x="22" y="531" font-size="11.5" fill="#8C8879">packed-bit circuits</text>
   </a>
   <a href="#stage-simplify">
   <title>Simplify and solve — click for a summary</title>
   <rect x="6" y="554" width="404" height="45" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1"/>
   <text x="22" y="574" font-size="14.5" fill="#46433A" font-weight="600">Simplify and solve</text>
   <text x="22" y="591" font-size="11.5" fill="#8C8879">equality propagation · the simplifier · linear bit-vector solve</text>
   </a>
   <a href="#stage-cbp-2">
   <title>Constant bit propagation — click for a summary</title>
   <rect x="6" y="614" width="404" height="45" rx="7" fill="#DFE8E3" stroke="#9CBAB1" stroke-width="1.5"/>
   <text x="22" y="634" font-size="14.5" fill="#3F6B63" font-weight="600">Constant bit propagation</text>
   <text x="394" y="634" font-size="10.5" fill="#3F6B63" text-anchor="end" font-style="italic">reaches a fixed point</text>
   <text x="22" y="651" font-size="11.5" fill="#8C8879">a second run, over the simplified formula</text>
   </a>
   <a href="#stage-intervals">
   <title>Interval and structural passes — click for a summary</title>
   <rect x="6" y="674" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1"/>
   <text x="22" y="694" font-size="14.5" fill="#46433A" font-weight="600">Interval and structural passes</text>
   <text x="22" y="711" font-size="11.5" fill="#8C8879">strength reduction · pure literals · ITE context · AIG core ·</text>
   <text x="22" y="726" font-size="11.5" fill="#8C8879">unconstrained elimination</text>
   </a>
   <a href="#stage-difficulty">
   <title>Difficulty check — click for a summary</title>
   <rect x="6" y="749" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1"/>
   <text x="22" y="769" font-size="14.5" fill="#46433A" font-weight="600">Difficulty check</text>
   <text x="22" y="786" font-size="11.5" fill="#8C8879">reverts to the unsimplified formula unless the estimated cost</text>
   <text x="22" y="801" font-size="11.5" fill="#8C8879">fell by a fifth, keeping any constants that were discovered</text>
   </a>
   <a href="#stage-array-transform">
   <title>Array transform — click for a summary</title>
   <rect x="6" y="824" width="404" height="60" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1" stroke-dasharray="5 3"/>
   <text x="22" y="844" font-size="14.5" fill="#46433A" font-weight="600">Array transform</text>
   <text x="22" y="861" font-size="11.5" fill="#8C8879">only with array operations — reads over writes become</text>
   <text x="22" y="876" font-size="11.5" fill="#8C8879">if-then-else chains</text>
   </a>
   <a href="#stage-cbp-3">
   <title>Constant bit propagation — click for a summary</title>
   <rect x="6" y="899" width="404" height="60" rx="7" fill="#DFE8E3" stroke="#9CBAB1" stroke-width="1.5"/>
   <text x="22" y="919" font-size="14.5" fill="#3F6B63" font-weight="600">Constant bit propagation</text>
   <text x="394" y="919" font-size="10.5" fill="#3F6B63" text-anchor="end" font-style="italic">reaches a fixed point</text>
   <text x="22" y="936" font-size="11.5" fill="#8C8879">a third run, which rewrites nothing: its fixed bits go to the</text>
   <text x="22" y="951" font-size="11.5" fill="#8C8879">bit-blaster, which drops the gates they determine</text>
   </a>
   <a href="#stage-bitblast">
   <title>Bit-blast to an AIG, then to CNF — click for a summary</title>
   <rect x="6" y="974" width="404" height="45" rx="7" fill="#FAF8EC" stroke="#C9C3A4" stroke-width="1.1"/>
   <text x="22" y="994" font-size="14.5" fill="#46433A" font-weight="600">Bit-blast to an AIG, then to CNF</text>
   <text x="22" y="1011" font-size="11.5" fill="#8C8879">ABC builds the circuit and shares equal subcircuits</text>
   </a>
   <a href="#stage-sat">
   <title>SAT solver — click for a summary</title>
   <rect x="6" y="1034" width="404" height="45" rx="7" fill="#E7E2C6" stroke="#C9C3A4" stroke-width="1.4"/>
   <text x="22" y="1054" font-size="14.5" fill="#46433A" font-weight="600">SAT solver</text>
   <text x="22" y="1071" font-size="11.5" fill="#8C8879">CaDiCaL, CryptoMiniSat, MiniSat or Riss</text>
   </a>
   <path d="M410 455 H432 V398 H410" fill="none" stroke="#3F6B63" stroke-width="1.3" marker-end="url(#ahl)"/>
   <text x="442" y="410.0" font-size="11" fill="#3F6B63">run once, then</text>
   <text x="442" y="423.0" font-size="11" fill="#3F6B63">repeated until</text>
   <text x="442" y="436.0" font-size="11" fill="#3F6B63">unchanged on</text>
   <text x="442" y="449.0" font-size="11" fill="#3F6B63">array-free input</text>
   <path d="M410 590 H432 V563 H410" fill="none" stroke="#3F6B63" stroke-width="1.3" marker-end="url(#ahl)"/>
   <text x="442" y="571.0" font-size="11" fill="#3F6B63">repeat until</text>
   <text x="442" y="584.0" font-size="11" fill="#3F6B63">unchanged</text>
   <path d="M410 1070 H432 V1043 H410" fill="none" stroke="#3F6B63" stroke-width="1.3" marker-end="url(#ahl)"/>
   <text x="442" y="1045.5" font-size="11" fill="#3F6B63">refine until no</text>
   <text x="442" y="1058.5" font-size="11" fill="#3F6B63">new axiom is</text>
   <text x="442" y="1071.5" font-size="11" fill="#3F6B63">needed</text>
   </svg>
   </div>
   <p class="pipe-hint">Click a stage for a summary of it.</p>

Nothing in the diagram is a separate program or a separate traversal of
the input from scratch: the formula is one hash-consed multigraph
throughout, and
each stage rewrites it in place. The node factory is already simplifying
as the parser builds the multigraph, so the formula reaching the first
stage has had the cheap local rewrites applied to it.

A session that has engaged the incremental driver does not come this way
at all. The driver keeps one SAT solver and one encoding alive across
queries and preprocesses what each ``check-sat`` added rather than the
whole formula, so the sequence above describes only the solves that
precede engagement, and those the driver declines to take. It engages on
the 32nd solve of a pure ``QF_BV`` or ``QF_ABV`` session and the third of
any other, or from the first with ``--incremental=on``, and never with
``--incremental=off``. :doc:`incremental-solving` describes what it does
instead.

The stages in detail
--------------------

Each box above links here. The stages are listed in the order the pipeline
runs them.

.. raw:: html

   <div class="pipe-detail" id="stage-input">
   <h4>SMT-LIB2 input</h4>
   <p>The front end parses the query into a directed acyclic multigraph, hash-consed so that two identical subterms are one node and every later pass can compare subterms by pointer. It is a multigraph because a node can take the same child more than once, as <code>bvadd x x</code> does. Nodes are not built verbatim: <code>SimplifyingNodeFactory</code> rewrites each one as it is created, so constant folding and the cheap local identities have already been applied by the time the first pass below runs.</p>
   </div>
   <div class="pipe-detail" id="stage-fp-prepare">
   <h4>Floating-point preparation</h4>
   <p>Reached only by a query that uses one of the floating-point theories. It makes the partial operations total, canonicalises the indexes of float-indexed arrays, and pins every rounding mode the formula names to one of the five legal encodings, before the formula is used for anything else. The test is per query rather than per session, so a float term that was popped, or built and never asserted, does not drag a later pure bit-vector query through a floating-point pass.</p>
   </div>
   <div class="pipe-detail" id="stage-array-equality">
   <h4>Array-equality lowering</h4>
   <p>An equality between two whole arrays is built as a single opaque node that survives function, <code>let</code> and query substitution unchanged. Here, at the complete-query boundary, each one still reachable is replaced by a fresh Boolean variable and its witness constraints are conjoined, which is what puts it into the refinement loop at the bottom of the pipeline. Two passes deliberately run just before the replacement, equality propagation and unconstrained elimination, because an equality that defines a symbol, or one with an unconstrained operand, is far cheaper to eliminate outright than to abstract and then refine. See <a href="array-extensionality.html">Array extensionality</a>.</p>
   </div>
   <div class="pipe-detail" id="stage-ackermann">
   <h4>Eager Ackermannisation</h4>
   <p>When fewer than ten array reads are reachable, or fifty if <code>--ackermannisation</code> was asked for, the reads are rewritten away here rather than left to the refinement loop. The bit-vector simplifications are more thorough than the array ones, so a formula with no arrays left in it gets a better pass than one that keeps them: nothing below eliminates unconstrained arrays, for instance, but everything eliminates unconstrained bit-vectors. Above that threshold the axioms are left to abstraction refinement, which adds only the ones a candidate model actually violates.</p>
   </div>
   <div class="pipe-detail" id="stage-cbp-1">
   <h4>Constant bit propagation</h4>
   <p>The first of three runs, on the formula roughly as written. Every node carries a vector of bits known to be zero, known to be one, or not yet known, and the transfer functions push that knowledge both from a node's children to the node and from the node back to its children: knowing that the result of <code>bvand</code> is all ones tells you that both operands are too. This is where the pipeline learns most of what it knows about individual bits. A worklist holds the nodes whose neighbours changed and each run drains it, so a run ends at its own fixed point rather than after a set number of sweeps. Fully determined nodes are replaced by their constant, with a fact conjoined to pin the node down so the constraint is not lost, and a contradiction found on the way — a bit required to be both zero and one — decides the query unsatisfiable without reaching the SAT solver. <code>--disable-cbitp</code> turns all three runs off.</p>
   </div>
   <div class="pipe-detail" id="stage-size-reducing">
   <h4>Size-reducing passes</h4>
   <p>A sequence chosen so that no pass in it can make the multigraph bigger. Each one can expose work for the others — eliminating an unconstrained variable can make an equality propagatable, which can fix more bits — so the sequence runs once and is then repeated until a round changes nothing. Rebuilding the analysis state each round is what makes the repeat expensive, so it is entered only for a formula with no array operations and fewer nodes than <code>--size-reducing-fixed-point-limit</code>; passing <code>-1</code> drops the size condition.</p>
   </div>
   <div class="pipe-detail" id="stage-fp-lower">
   <h4>Floating-point lowering</h4>
   <p>Floating-point operations become circuits over packed bits. This sits after the size-reducing passes rather than before them because those passes want to see a float symbol rather than its exposed bits, unconstrained elimination in particular. Symbols, constants and reads keep their sort metadata so that a model can be reconstructed afterwards. The only floating-point operations that survive are the predicates, which the bit-blaster encodes natively over the packed bits.</p>
   </div>
   <div class="pipe-detail" id="stage-simplify">
   <h4>Simplify and solve</h4>
   <p>The main simplification loop: equality propagation, then the general simplifier, then the linear bit-vector equation solver, repeated until a round returns the formula it started with. Because the multigraph is hash-consed that comparison is a pointer comparison, not a traversal. Unlike the size-reducing sequence above this loop is not guarded by a size limit, its passes being the ones that shrink formulas most reliably.</p>
   </div>
   <div class="pipe-detail" id="stage-cbp-2">
   <h4>Constant bit propagation</h4>
   <p>The second run. Repeating the analysis pays here because the loop above has rewritten the formula enough that bits which were not derivable the first time often are: substituted equalities and solved linear equations both expose constants the first run could not see.</p>
   </div>
   <div class="pipe-detail" id="stage-intervals">
   <h4>Interval and structural passes</h4>
   <p>Passes that use what the analyses now know, or that restructure the formula in ways the earlier passes cannot. Strength reduction reads the fixed bits and the unsigned intervals together and swaps operations for cheaper ones rather than for constants: a signed division whose operands are known to share a sign bit becomes an unsigned division, an arithmetic right shift whose sign bit is known to be zero becomes a logical one, and a sign-extension whose sign bit is fixed becomes a concatenation with a constant. The rest work on the Boolean structure — pure literals, if-then-else context, and a propositional core simplified through an AIG.</p>
   </div>
   <div class="pipe-detail" id="stage-difficulty">
   <h4>Difficulty check</h4>
   <p>Simplification does not always help, so the estimated cost of the formula is compared against the estimate taken before the loops ran. Unless it fell by at least a fifth the whole simplification is discarded and the earlier formula is used instead. Constants discovered along the way are kept and re-applied, since assigning a variable a constant cannot make the problem harder. The estimator is calibrated against the number of AIG nodes the bit-blaster really builds.</p>
   </div>
   <div class="pipe-detail" id="stage-array-transform">
   <h4>Array transform</h4>
   <p>Reads are rewritten through the writes above them, so a read of a written array becomes an if-then-else on whether the two indexes are equal, and array terms disappear from the formula handed to the bit-blaster. The axioms relating two reads of the same array at possibly-equal indexes are not emitted here: that is what the refinement loop at the bottom is for.</p>
   </div>
   <div class="pipe-detail" id="stage-cbp-3">
   <h4>Constant bit propagation</h4>
   <p>The third run differs from the other two in that it does not rewrite the formula at all. Its fixed-bit map is handed to the bit-blaster, which emits no gates for the bits already known — the same information spent on making the encoding smaller rather than on making the formula smaller. Because that map has to describe exactly the tree the bit-blaster receives, no pass may run between this point and bit-blasting.</p>
   </div>
   <div class="pipe-detail" id="stage-bitblast">
   <h4>Bit-blast to an AIG, then to CNF</h4>
   <p>Each bit-vector operation becomes a circuit of and-gates and inverters. ABC builds and structurally hashes that graph, so equal subcircuits are built once however many times they appear, and then converts it to CNF. <code>--cnf-generation-effort</code> chooses how hard the conversion works at finding a smaller clause set.</p>
   </div>
   <div class="pipe-detail" id="stage-sat">
   <h4>SAT solver</h4>
   <p>The clauses go to whichever backend the build has and the command line selects. If the formula still contains array operations the encoding is deliberately incomplete: it omits the axioms saying that two reads at equal indexes return equal values. A satisfiable answer is therefore checked against those axioms, and any the candidate model violates are added to the live solver before it is asked again, until a model satisfies all of them. An unsatisfiable answer needs no check, since adding axioms can only remove models.</p>
   </div>

Where it repeats
----------------

Three parts of the pipeline run more than once, for three different
reasons.

**The size-reducing passes** run once unconditionally, and are then
repeated until they stop changing the formula. Each pass can expose work
for the others -- eliminating an unconstrained variable can make an
equality propagatable, which can fix more bits -- so one sweep leaves
easy reductions on the table. The repeat is not free, because the state
is discarded and rebuilt each time, so it is only entered for a formula
with no array operations and fewer nodes than
``--size-reducing-fixed-point-limit``. Passing ``-1`` removes the size
condition.

**The simplify-and-solve loop** repeats for the same reason but is not
guarded, because its passes are the ones that shrink the formula most
reliably. It stops as soon as a round returns a formula equal to the one
it started with. Since the multigraph is hash-consed, that comparison is
a pointer comparison.

**Array refinement** is not a simplification at all. When the formula
still contains array operations, the encoding handed to the SAT solver
under-constrains them: it omits the axioms saying that two reads at equal
indices return equal values. If the solver reports satisfiable, the
candidate model is checked against those axioms, and any that it violates
are added to the live solver before it is asked again. The loop ends when
the model satisfies every axiom, or the solver reports unsatisfiable --
which needs no check, since adding axioms can only remove models. With
``--array-equality`` the same loop carries the extensionality procedure's
lemmas instead.
