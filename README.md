# Soundness of Wasm bounds check elimination: a Rocq model

This is a Rocq (Coq 8.20) formalization of the soundness argument of the
analysis in V8's Turboshaft Wasm bounds check elimination
(`src/compiler/turboshaft/wasm-bounds-check-elimination-reducer.{h,cc}`,
branch `bce-loop-ideas`, commit `60f7a3c58ab`, whose comments state the
conditions used here since `a0dc7a91d88`). It covers the
part of the argument that is not arithmetic: why a fact recorded at a
program point still holds at the later points where the analysis uses
it. The arithmetic of each rule is checked separately with Z3 (see
"Z3 checks" below). Here it stays abstract.

This repository also holds the other checks of the analysis that are not
part of V8: the Z3 scripts (`z3/`), which follow the CL series (branch
`bce-series`, commit `135eafb4cf9`), the planted-bug driver
(`planted-bugs/`), which measures how well V8's random tests find bugs,
and a probe of the pipeline (`probes/`).

Build with `make` (it calls `coq_makefile`). `make assumptions` prints the
axioms the main theorems depend on. Only the standard library is used.

| File | Content |
|---|---|
| `Graph.v` | Paths, dominance, and its basic properties |
| `Persistence.v` | Milestone 1: abstract executions, facts, and the persistence theorem |
| `Loops.v` | Milestone 2: facts recorded at loop headers (per-edge obligations) |
| `Canonical.v` | Milestone 3: pure operations, canonical terms, the GVN invariant, facts over terms |
| `Induction.v` | Milestones 2 and 3 together: induction on a loop phi with per-edge phi semantics |
| `Alias.v` | Milestone 4: length aliases (`TryResolveMergeBound`) |
| `Assumptions.v` | `Print Assumptions` of the main theorems (not part of `make all`) |

All four milestones are complete. There is no `Admitted` and no axiom
other than `Classical_Prop.classic` (excluded middle).

## The model

### Graph and dominance (`Graph.v`)

Program points form a graph: `succ : point -> point -> Prop`, with an
`entry` point. `path x y l` means that `l` lists the points of a path
from `x` to `y`, both included. Dominance is the usual notion on the
whole graph, back edges included:

```coq
Definition dom (d q : point) : Prop := forall l, path entry q l -> In d l.
```

The file proves reflexivity, transitivity, antisymmetry on reachable
points (`dom_antisym`), that `entry` dominates everything, that a strict
dominator of `q` dominates the predecessors of `q` (`dom_pred`), and that
if `d` does not dominate `q`, some path to `q` avoids `d` (`not_dom_path`,
which uses excluded middle).

A point can be read as an operation. The operations of a block form a
chain, and the phis of a block are defined at its first point.

### Executions (`Persistence.v`)

An execution is a finite prefix: `pts : nat -> point`, `env : nat -> var
-> val`, `len : nat`. `pts 0 = entry`, each step follows `succ`, and
arriving at a point writes only the variables defined there. Each SSA
variable is defined at exactly one point, `def : var -> point`:

```coq
ex_frame : forall k v, k < len -> pts (S k) <> def v -> env (S k) v = env k v
```

`env k` is the environment just after arriving at `pts k`. The values
written are not constrained, so this abstracts any semantics.

### Facts

Facts are abstract: `holds : fact -> (var -> val) -> Prop`, with
`leaves : fact -> list var`, and `holds` depends only on the values of the
leaves (`holds_ext`).

- `R p F`: the fact `F` is recorded at `p`. It holds on arrival at `p`:
  past a `TrapIf`, at a branch target, at a loop header.
- `A q F := exists p, dom p q /\ R p F`: the facts known at `q`. This
  models the snapshot tables: `BeginBlock` starts a block from the common
  ancestor of the predecessors' snapshots, which is the snapshot of a
  dominator (for a loop header, because it dominates its back edge: see
  the comment in `BeginBlock`).
- Leaves condition (`leaf_ok p v := ~ (dom p (def v) /\ def v <> p)`): no
  leaf of a fact recorded at `p` is defined at a point that `p` strictly
  dominates. `leaves_ok` requires this for every fact recorded at a
  reachable point. It holds for leaves defined at dominators of `p`
  (`dom_leaf_ok`). It also holds for leaves defined at points that some
  dominator `p0` of `p` does not dominate (`not_dom_leaf_ok`), which is
  the case for length aliases.
- Local justification (`justified_at e p F`): whenever `pts k = p`, `F`
  holds in `env k`, provided that all the facts known at all earlier
  times held then (`hyps_before e k`). This is the proof obligation of
  each rule of the analysis.

### Canonical values (`Canonical.v`)

Some variables are pure operations: `op x = Some (f, args)`. Their
arguments are defined at dominators of `def x` (SSA; non-strict dominance
is enough). When `def x` is reached, `x` is written with
`eval_fn f (map env args)` (`pure_sem`). `comm f` marks commutative
operations and `ident f` marks identities (casts, `AssertNotNull`, type
annotations, load-elimination replacements).

Terms are `Leaf v | App f ts`. `canon x t` is a relation, not a function,
so it covers the choices made by `CanonicalValue`:

- any variable can be a leaf (phis, loads, parameters, and operations
  beyond the depth limit);
- a pure operation can be decomposed (`canon_app`);
- the arguments of a commutative operation can be swapped (`canon_comm`);
- an identity is its argument (`canon_alias`).

Facts over canonical terms are `tfact = {tf_pred : list val -> Prop;
tf_args : list term}`, with `tholds F en := tf_pred F (map (eval en)
(tf_args F))`. Their leaves are the leaves of the terms. The facts of
the analysis all have this form, with an abstract predicate:

- bounds checks `base + [lo, hi] < l`;
- non-negative offsets;
- min lengths `l >= m`;
- length aliases `x = l - r`;
- the branch and trap conditions themselves.

## Main theorems

### Milestone 1: persistence (`Persistence.v`)

```coq
Theorem soundness :
  forall e, leaves_ok -> justified e ->
  forall k F, k <= len e -> A (pts e k) F -> holds F (env e k).
```

The proof is by strong induction on `k`. Take the last time `t <= k` at
which `p` (a dominator of `pts k` that recorded `F`) was visited. `F`
held at `t`, by local justification and the induction hypothesis. Then
`persistence` shows that no leaf of `F` was written between `t` and `k`.
A write at time `s` is a visit of `def v`, which `p` does not dominate, so
some path to `def v` avoids `p`. Following it with the execution from `s`
to `k`, which does not visit `p` again, gives a path to `pts k` that
avoids `p`. That contradicts `dom p (pts k)`.

Supporting results:

- `known_at_arrival`: while justifying a fact at time `k`, the facts
  recorded at strict dominators of `pts k` can be used at time `k`.
  This covers facts recorded earlier in the same block, as the C++ does
  when it processes a block's operations in order.
- `justified_at_seq`: the facts recorded at one point can be justified in
  sequence: later phis of a loop header use facts recorded for earlier
  ones (see the comment of `ProcessLoopHeader`).
- `A_mono`: adding (ghost) facts to `R` only adds known facts, such as
  induction invariants stronger than the facts the analysis records (see
  the comment of `ProcessLoopHeader`).

### Milestone 2: loop headers (`Loops.v`, `Induction.v`)

The setting is a header `h` with a forward predecessor `f` and a back
edge from `b`, where `h` dominates `b` and `h <> entry`.

- `fwd_dom_header`: the dominators of `f` dominate `h`.
- `known_at_header`: `A h F <-> A f F \/ R h F`. What is known at the
  header is what is known at the end of the forward predecessor, plus what
  the header records. The back edge is ignored, as in `BeginBlock`.
- `edge_ok e pred F`: on arrival at `h` from `pred` at time `k`, `F`
  holds if the facts known at `pred` held at `k - 1`. For the back edge,
  those facts include the facts recorded at `h`, by
  `header_known_at_back`; this is the induction hypothesis.

```coq
Theorem loop_justified :
  forall e F, edge_ok e f F -> edge_ok e b F -> justified_at e h F.
Lemma invariant_back_ok :   (* loop-invariant facts: back edge for free *)
  forall e F, R h F -> (forall v, In v (leaves F) -> def v <> h) -> edge_ok e b F.
```

`Induction.v` adds the semantics of a loop phi `i = phi(i0, inext)`,
taking `i0` from `f` and `inext` from `b`. `phi_fact_justified` reduces
the per-edge obligations to statements about values only
(`arrival_obligation`): if the facts known at the predecessor hold in
`en`, and `en'` is `en` with `i` set to the value of the input's
canonical term, then `F` holds in `en'`. With `tn = i + c`, these are the
Z3 lemmas ([induction-constant], [induction-not-equal],
[induction-decreasing], ...). This is the argument of the comment of
`ProcessLoopHeader`: "The value of {i} they tested is the current one,
since the header, where {i} is defined, is not executed again before the
back edge."

### Milestone 3: canonical values (`Canonical.v`)

```coq
Theorem canon_sound :
  forall e, pure_sem e -> forall x t, canon x t ->
  forall k, k <= len e -> dom (def x) (pts e k) ->
  env e k x = eval (env e k) t.
```

At any time, a variable whose definition dominates the current point has
the value of its canonical term, for the current values of the leaves.
This is the invariant of Barthe, Demange and Pichardie (TOPLAS 2014). The
proof uses mutual induction on `canon`, and the persistence lemma of
Milestone 1 with `p := def x`.

- `same_canonical_value` is the claim of the comment of
  `CanonicalValue`, nearly literally. Let `t0` be the last visit of `p`
  before `k`, where `p` dominates `pts k`. A variable used at `pts k` with
  the same canonical term as a variable used at `p` has the value that
  variable had at `t0`.
- `record_ssa_fact`: a condition on SSA values at the current point is a
  fact over their canonical terms.
- `ssa_fact_leaves_ok`: such a fact satisfies the leaves condition.
- `known_fact_on_ssa_values`: a known fact over canonical terms gives the
  condition on any SSA values at the current point with these canonical
  terms. This instantiates Milestone 1.

### Milestone 4: length aliases (`Alias.v`)

The setting is a merge `m` (not a loop header) with a phi `phi`. `m`
dominates `f`, and `m <> h`. The remaining input `y` (an array length plus
a constant, with canonical term `ty`) comes from predecessor `pL`, and
`~ dom m pL`, since a merge does not dominate its predecessor. On the
other edges, the phi takes an `Excluded` value, a constant ruled out by
the entry condition. The facts known at `f` imply `~ Excluded phi`. The
alias fact `Fa` has leaves `phi` and the leaves of `ty`, and holds when
`phi = eval ty`.

- `leaves_y_not_dom_m`: the leaves of `ty` are not dominated by `m`.
- `leaves_y_ok`: any fact recorded at a point dominated by `m` satisfies
  the leaves condition for these leaves. In particular, this holds for
  the facts about the array derived from the alias inside or after the
  loop.
- `alias_leaves_ok`: the leaves condition for `Fa` at `h`.
- `alias_fwd`: the forward-edge obligation. The last execution of `m`
  before entering the loop took the edge of `y` (the other edges are
  ruled out by the entry condition, using `phi`'s value, which has not
  changed since). The leaves of `ty` were not written at `m`, nor since.
- `alias_back`: `Fa` is loop-invariant.
- `alias_justified`: `Fa` is locally justified at `h`.
- `justified_using_alias`: a fact recorded at the header after the alias
  may use the alias at the same time.
- `alias_sound`: end to end. If the other recorded facts satisfy the
  leaves condition and are justified, then the alias holds at every point
  dominated by `h`.

## Mapping to the C++

| Model | C++ |
|---|---|
| `A q F` (facts recorded at dominators) | snapshot tables `known_bounds_checks_`, `known_non_negative_offsets_`, `known_min_lengths_`, `known_length_aliases_`; `BeginBlock` merges at the common ancestor; back edges ignored |
| `R p F` at the point after a trap / at a branch target | `ProcessTrapIf`, `ProcessBranch` → `ProcessCondition` |
| `R h F` at a loop header | `ProcessLoopHeader`, `ProcessDecreasingInduction`, `RecordLoopBound` |
| `R h Fa` | `TryResolveMergeBound` (`known_length_aliases_.Set`) |
| ghost facts in `R` | raw branch conditions collected by `ForEachDominatingCondition` (`ProcessLoopHeader`, `EntryLowerBound`); induction invariants such as `i <= x` |
| `canon x t`, `term` | `CanonicalValue` (`values_by_structure_`), `ResolveReplacements`, `ResolveAliases` |
| `ident` operations | `WasmTypeCast`, `AssertNotNull`, `WasmTypeAnnotation`, load-elimination replacements |
| pure operations | `WordBinop`, `Shift`, `Change`, `Constant`, `ArrayLength`, `TaggedBitcast` of Smis |
| `edge_ok`, `phi_fact_justified` | the induction arguments in the comments of `ProcessLoopHeader` and `ProcessDecreasingInduction` |
| `alias_fwd` | the path argument in the comment of `TryResolveMergeBound` |
| abstract `tf_pred`, `Excluded`, `alias_arith`, the obligations | the Z3 lemmas |

## Assumptions and what is not modeled

- **Arithmetic is abstract.** Fact predicates, the per-edge obligations of
  loop facts, `Excluded` / `entry_cond`, and `alias_arith` are hypotheses.
  They correspond to the Z3 lemmas and to the decisions of the analysis
  (which candidates it accepts), which are not modeled.
- **The analysis algorithm is not modeled.** There are no snapshot
  tables, `OffsetRange` hulls or `ForEachCondition`. The tables are
  modeled by `A` (facts recorded at dominators). It is assumed, not proved
  from the code, that the facts the analysis uses at a point are among
  those recorded at its dominators. The `BeginBlock` comment argues this.
- **Semantics are abstract.** Nothing constrains the values written,
  except for pure operations (`pure_sem`) and, where needed, phis
  (`phi_sem` in `Induction.v` and `Alias.v`). The justification of a
  trap or branch fact (that the condition holds past the trap or at the
  target) is an obligation for each fact, not derived from a semantics of
  traps and branches.
- **Graph assumptions are hypotheses** (Turboshaft invariants):
  - loop headers have exactly a forward and a back-edge predecessor, and
    dominate the back edge (`ProcessLoopHeader` gives up otherwise);
  - a merge that is not a loop header does not dominate its predecessors
    (`m_not_dom_pL`): an edge to a block that dominates its source is a
    back edge, and only loop headers have back edges;
  - branch targets have a single predecessor (edge-split form), which is
    implicit in modeling branch conditions as facts recorded at the target;
  - phis are defined at the first point of their block, and have one
    input per incoming edge.
- **Pure operations must be deterministic functions of their inputs'
  values at the time they execute.** This is why `TaggedBitcast` of a
  heap reference (which a moving GC can change) is a leaf, and why
  `ArrayLength` is pure (array lengths never change).
- **The transformation is not modeled.** The theorems are about the
  analysis on the input graph: every fact the analysis uses holds in every
  execution of that graph. Removing redundant traps, and the fallback
  sequences (`FallbackInstructionSequence`), are not modeled.
- **Representatives and the depth limit.** `CanonicalValue` identifies
  values through representatives (the first operation with a given
  structural key) and stops at depth 16. The model uses terms instead. The
  link: an `OpIndex` that appears as a cut-off leaf in a key is an input,
  so it dominates the point where the key is computed. There its value is
  that of its own structure (`canon_sound`). So a key denotes the same
  fully unfolded term wherever it is computed, and two operations with the
  same key have the same full unfolding, up to commutative swaps. The full
  unfolding is a `canon` derivation, so the C++ identification is covered
  by `same_canonical_value`. This argument is not mechanized.

## Z3 checks (`z3/`)

Install the solver with `pip install -r requirements.txt` (in a venv).

- `check-z3-lemmas.py <header>` checks the lemmas written in the comments
  of `wasm-bounds-check-elimination-reducer.h`: each one must be
  unsatisfiable, and its assumptions satisfiable.
- `check-z3-decisions.py <v8 dir> [--from <name>]` checks the code that
  applies the lemmas. The decision functions of the analysis are
  transcribed as z3py functions over 32-bit bitvectors. It first checks
  that the transcribed lines are still in the source (anchors, ignoring
  whitespace), and stops if one is missing. About 2 minutes. It checks:
  - **soundness**: from facts that hold and a condition that holds, the
    facts the code records hold, and a check found redundant cannot fail;
  - **well-formedness** (W1-W8): whatever the facts, the ranges the code
    builds are valid and the DCHECKs on values hold. This matters in
    unreachable code, where facts can contradict each other. W8 models
    every path by which a length key reaches `MinLength`, including an
    `ArrayLength` replaced by load elimination with any constant;
  - **refutations**: counterexamples showing why the code excludes a case
    (narrowing a negated or signed comparison, a constant length key of
    2^30 or more in `MinLength`).

  `INVENTORY` counts the `OffsetRange` constructions, the DCHECKs and the
  calls to `MinLength` and `LengthKey` in the source: when a count
  changes, the script stops, so that the new use is reviewed. What is
  outside Z3: the structural DCHECKs (graph shape, processing order,
  representations), which the random tests exercise.

## Planted bugs (`planted-bugs/`)

`plant-bugs.py [--set loops|persistence|truncation|narrowing|dchecks]
[names...]` plants bugs in the analysis (one-line edits of the source,
restored at the end), rebuilds `d8` for each one, and measures how long
the random loop test (`test/mjsunit/wasm/bounds-check-elimination-loops.js`)
takes to find it, with the verifier on and 8 workers, and whether
`bounds-check-elimination.js` finds it. `V8_DIR` (required) is the V8
checkout, `V8_BUILD_DIR` its build directory (default `out/x64.optdebug`),
`BUDGET` the seconds of fuzzing per bug (240), and `FUZZ_DIR` where the
results go (`./plant-bugs-results`). An edit that no longer matches the
source is reported, and must be updated. The sets:

- `loops`: the loop rules (induction, not-equal bounds, entry lower
  bounds, length aliases);
- `persistence`: canonical values, snapshot merges, forms of conditions;
- `truncation`: truncated 64-bit additions;
- `narrowing`: narrowed 64-bit comparisons, and the reading of 64-bit
  values as their truncations;
- `dchecks`: checks that seem redundant, turned into DCHECKs, to see
  whether they can fail.

## Probes (`probes/`)

`check-normalization.py <v8 dir> [<d8>]` checks that the default
pipeline moves constants to the right of additions before the analysis,
which only reads `x + c` (the CL series dropped `c + x`). After `a[i]`, the
check of `a[1 + i]` must be recognized like `a[i + 1]`. The normalization
comes from loop peeling, so with `--no-wasm-loop-peeling` the analysis
loses precision on `c + x` (reported for information). It needs a debug
or optdebug `d8`, for the trace flag. No V8 test can check this: the unit
tests do not run the pipeline, and mjsunit tests only see results.

## What remains open

- **Connect the analysis to `A`.** Model the analysis algorithm (or its
  per-rule decisions) and prove that each fact it uses at a point is
  recorded at a dominator. This means modeling snapshot merging.
- **Instantiate the abstract predicates and obligations.** Use 32-bit
  arithmetic (for instance with `Z` modulo 2^32) and prove the Z3 lemmas
  in Rocq, so that `tf_pred`, `Excluded` and the obligations become
  concrete.
- **Model trap and branch semantics.** That would discharge the
  justification of condition facts.
- **Mechanize the representative / depth-limit argument** (see above).
- **Model the transformation.** Trap removal and fallback sequences, with
  a simulation argument.
