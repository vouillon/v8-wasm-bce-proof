# Soundness of Wasm bounds check elimination: a Rocq model

This is a Rocq (Coq 8.20) formalization of the soundness argument of the
analysis in V8's Turboshaft Wasm bounds check elimination
(`src/compiler/turboshaft/wasm-bounds-check-elimination-reducer.{h,cc}`,
branch `bounds-check-elimination`, commit `b02d02c359a`). It covers the
part of the argument that is not arithmetic: why a fact recorded at a
program point still holds at the later points where the analysis uses
it. The arithmetic of each rule is checked separately with Z3 (lemmas in
the header comments, `check-z3-decisions.py`). Here it stays abstract.

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
  dominator (see "Findings", item 6 for loop headers).
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
  sequence (see "Findings", item 3).
- `A_mono`: adding (ghost) facts to `R` only adds known facts (see
  "Findings", item 2).

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
  those recorded at its dominators. The `BeginBlock` comment argues this
  (see "Findings", item 6).
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

## Findings: imprecisions and gaps in the informal arguments

1. **Facts derived from length aliases do not satisfy the premise of the
   `CanonicalValue` argument.**
   - The `CanonicalValue` comment argues: "The operations whose canonical
     value is not structural (phis, loads, parameters...) used at {p} are
     defined in dominators of {p}". The `BeginBlock` comment relies on it:
     "facts known at the start of a block were recorded in its
     dominators, as {CanonicalValue} requires".
   - Facts derived from a length alias break this premise. When
     `TryExtractArrayLength` resolves `x` to `l - r` through
     `known_length_aliases_`, the analysis records facts keyed by
     `LengthKey(l)` at points `p` inside or after the loop:
     - bounds checks (`ProcessBoundsCheck`, and `RecordLoopBound` /
       `ProcessDecreasingInduction` at the header);
     - min lengths (`RecordMinLength`).

     The leaves of these facts (the array, or whatever `l`'s canonical
     value bottoms out at) are defined before the merge, at points that do
     not dominate `p`.
   - The only justification given is the `LengthAliasMap` comment: "Facts
     about the array learnt from it are still sound, since they are about
     values". That covers the fact holding when it is recorded. It does
     not cover the fact persisting from `p` to the points `q` that `p`
     dominates. The `TryResolveMergeBound` comment argues persistence for
     the alias itself, not for the facts derived from it.
   - Formalizing showed what makes them sound. The right condition is
     not "leaves defined at dominators of `p`" but "no leaf defined at a
     point strictly dominated by `p`" (`leaf_ok`). Alias-derived facts
     meet it because `p` is dominated by the merge `m` and the leaves are
     not (`leaves_y_ok`, from `~ dom m pL`, i.e. the merge is not a loop
     header).
   - The conclusion is right, but the informal argument should state the
     general condition, or extend the `CanonicalValue` and `BeginBlock`
     comments to these facts.
2. **The loop induction is on invariants stronger than the recorded
   facts.**
   - The `ProcessLoopHeader` comment says "These facts are recorded at the
     header, so they must hold whenever the header is executed, which is
     shown by induction on the iterations". For a not-equal bound whose
     `x` is not an array length, the only recorded fact is `0 <= i`. That
     fact is not inductive on its own: `i != x` does not prevent
     `i + 1` from overflowing.
   - The induction is on `0 <= i <= x` ([induction-not-equal]), which the
     comment mentions ("{i} is then at most {x}") but does not record.
     Likewise, decreasing not-equal loops need `y <= i <= i0`
     ([induction-decreasing-not-equal]).
   - In the model, such invariants are ghost facts added to `R`
     (`A_mono`). They must satisfy the leaves condition themselves: `x`
     and `i0` are computed before the loop, which `FindNotEqualBound` and
     the forward-input argument ensure. `y` is a constant.
3. **Facts recorded at the same header in the same visit can depend on
   each other.**
   - `ProcessLoopHeader` processes the phis in order. An increasing phi
     can record an alias (`RecordLoopBound` → `TryResolveMergeBound`). A
     later decreasing phi of the same header can then resolve its start
     `i0 = x` through that alias (`EntryLowerBoundOfStart` and
     `TryExtractArrayLength` in `ProcessDecreasingInduction`).
   - Similarly, `EntryLowerBoundOfStart` reads `MinLength`, which
     includes the min lengths recorded at the header in the same visit by
     `RecordLoopBound` or `ProcessDecreasingInduction` for an earlier phi.
     That reads the current table at the header, not what is known at the
     end of `forward`, despite the "when entering the loop from
     {forward}" of its comment.
   - The forward-edge justification of the second fact then uses the
     alias or min length at the same time, not at an earlier one. The "induction on
     iterations" argument has to be on the facts of the header taken
     together, justified in recording order. This is sound because each
     fact's forward justification only uses facts from earlier times or
     facts recorded before it at the header (`justified_at_seq`,
     `justified_using_alias`).
4. **The `ProcessLoopHeader` and `EntryLowerBound` reasoning uses raw
   branch conditions, not the tables.**
   - `ForEachDominatingCondition` walks the dominator chain and
     reinterprets branch conditions with `CanonicalValue`. These
     conditions are not stored in the snapshot tables.
   - In the model, they are ghost facts recorded at the branch targets
     (a target has a single predecessor). The "conditions collected
     below held when they were tested" then becomes "they hold at the
     back edge for the current values" by Milestone 1. The comment
     argues this only for `i`. For the other operands, such as `x` in
     `i < x`, it needs the same persistence argument: `x`'s leaves
     dominate the branch target.
5. **`TryResolveMergeBound`: what must not be recomputed is the leaves of
   `l`'s canonical value.**
   - The comment says "Neither {l} nor its array is computed again
     before {b}" and concludes that "{x} is {l} minus a constant, for the
     current values of {l} and of its array". But `l` does not dominate
     `b`, so it has no meaningful "current value" there. What matters is
     the value of `l`'s canonical term at the current leaves. Those
     leaves can differ from "its array": for instance, the object behind
     casts (`ResolveAliases`), or the leaves of a load-elimination
     replacement of the length.
   - The argument also needs the leaves not to be defined at `m` itself,
     so that their values at the end of `pL` are those after `m`. This
     follows from `~ dom m pL` too (`leaves_y_not_m`).
   - The formal version (`alias_fwd`) states the alias as
     `phi = eval ty` with `ty` the canonical term of the remaining input.
6. **`BeginBlock`, loop headers.**
   - "this common ancestor is the snapshot of a block that dominates all
     the (forward) predecessors, and thus the current block". For a loop
     header, dominating the forward predecessor does not by itself mean
     dominating the header, since the back edge is another way in. It
     does because the header dominates the back edge: a path to the
     header first enters it from the forward predecessor
     (`fwd_dom_header`, `known_at_header`).
   - The same lemma shows why facts known at the header (recorded before
     the loop) have no leaf defined inside the loop. The comment's "These
     facts are about values computed before the loop" is close, but the
     property used is the leaves condition: alias leaves are computed
     before the loop without dominating it.
7. **The `CanonicalValue` argument is one level deep.**
   - "A value used at {q} with the same canonical value is computed from
     these same operations, and so is equal to the value used at {p}".
     This needs the invariant that every pure operation whose definition
     dominates `q` has, at `q`, the value of its term for the current
     leaves.
   - That invariant needs an induction on the term (`canon_sound`). It
     relies on the leaves of each sub-term dominating the sub-term's
     definition, not only on the leaves dominating `p`.
   - With the depth limit and representatives (see above), "computed from
     these same operations" is not literally true. A cut-off leaf at `q`
     may be a different operation computing the same structure. The
     conclusion still holds.

No unsoundness was found. Every gap above is an imprecision or an
unstated step in an argument whose conclusion holds under the stated
graph invariants.

## `Print Assumptions` (output of `make assumptions`)

```
Persistence.soundness               Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Persistence.known_at_arrival        Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Loops.loop_justified                Closed under the global context
Loops.invariant_back_ok             Closed under the global context
Canonical.canon_sound               Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Canonical.same_canonical_value      Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Canonical.known_fact_on_ssa_values  Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Induction.phi_fact_justified        Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Alias.alias_leaves_ok               Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Alias.alias_justified               Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
Alias.alias_sound                   Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

Excluded middle is used for:

- the existence of a path avoiding a non-dominator;
- the last visit of a point;
- prefixes of paths at a first occurrence;
- case splits on point equality.

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
