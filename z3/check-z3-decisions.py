# Usage: check-z3-decisions.py <v8 dir> [--from <name>]
# With --from, the queries before the first one whose name contains
# <name> are skipped. The whole check takes about 5 minutes. The anchors
# are those of the CL series (branch bce-series-v3, head e5eb75d2633), which
# differs from the bce-loop-ideas prototype in a few places (MinLength's
# DCHECK, no constant on the left of 32-bit or truncated additions).
#
# Checks with Z3 that the decision functions of Wasm bounds check
# elimination keep its facts sound. The functions are transcribed below
# from src/compiler/turboshaft/wasm-bounds-check-elimination-reducer.{h,cc}
# as closely as possible (32-bit bitvectors, with the signed and unsigned
# operations of the C++ code). Each query states that, from facts that
# hold and a condition that holds, the facts computed by the code hold,
# or that a check found redundant cannot fail, and must be unsat. The
# assumptions of each query must also be satisfiable.
#
# The well-formedness queries (W1...) check what must hold whatever the
# facts, since facts may contradict each other in unreachable code: the
# ranges the code builds are valid, and the DCHECKs on values hold. The
# script also counts the uses of OffsetRange and the DCHECKs in the
# source (INVENTORY), so that new ones are reviewed.
#
# The lemmas in the comments of the header (check-z3-lemmas.py) are
# about the mathematical arguments; these queries are about the code
# that applies them. To detect when the code changes, the script first
# checks that the lines of code it transcribes are still in the source
# (see ANCHORS): update the transcription when one of them is missing.
#
# Facts, for a base value {x} and an array of length {l} (l < 2^30):
# - a range of offsets [lo, hi] within bounds: x + k <u l for all k in
#   [lo, hi] (KnownBoundsChecks);
# - a range of non-negative offsets [lo, hi]: x + k >=s 0 for all k
#   (KnownNonNegativeOffsets);
# - a minimal length m: l >=u m (KnownMinLengths).
# Ranges are valid ranges in the sense of {OffsetRange::IsValidRange},
# and "k in [lo, hi]" is {OffsetRange::Contains}. Assumptions about
# ranges are stated on their bounds; [range-endpoints] shows that this
# is the same as stating them for all their offsets.
import os, re, sys, time
from z3 import (And, BitVec, BitVecVal, Bool, BoolVal, Extract, If, Implies,
                Not, Or,
                SignExt, SolverFor, UGE, UGT, ULE, ULT, ZeroExt, sat, unsat)

if len(sys.argv) < 2:
    sys.exit('usage: check-z3-decisions.py <v8 dir> [--from <name>]')
V8 = sys.argv[1]
START = sys.argv[3] if len(sys.argv) > 3 and sys.argv[2] == '--from' else None
SRC = 'src/compiler/turboshaft/wasm-bounds-check-elimination-reducer'

# Lines of code transcribed below (whitespace is ignored).
ANCHORS = {
    'h': [
        'return static_cast<int32_t>(upper - lower) >= 0;',
        'if (IsValidRange(lower_, offset) && IsValidRange(offset, upper_)) {',
        'if (IsValidRange(upper_, offset) && IsValidRange(lower_, offset)) {',
        'if (IsValidRange(offset, lower_) && IsValidRange(offset, upper_)) {',
        'uint32_t second_lower = second->lower_ - first->lower_;',
        'uint32_t second_upper = second->upper_ - first->lower_;',
        'if (second_lower > second_upper) continue;',
        'uint32_t size = std::max(first->upper_ - first->lower_, second_upper);',
        'if (static_cast<int32_t>(size) < 0) continue;',
        'if (!result.has_value() || size < result->upper_ - result->lower_) {',
        'return {!lower_implied, lower_implied || !upper_implied};',
        '(position == OffsetRange::RelativePosition::kAbove && '
        'OffsetRange::IsValidRange(facts.upper(), offsets.upper()));',
        '(position == OffsetRange::RelativePosition::kBelow && '
        'OffsetRange::IsValidRange(offsets.lower(), known.lower()));',
        'static constexpr bool kSingleComparisonTwoSidedGuard = Is64();',
        'V<Word64> end = __ Word64Add(__ ChangeUint32ToUint64(start), '
        '__ Word64Constant(uint64_t{size}));',
        'GOTO_IF_NOT(LIKELY(__ Uint32LessThan(index, length)), fallback_code);',
        'GOTO_IF_NOT(LIKELY(__ Uint64LessThan(end, '
        '__ ChangeUint32ToUint64(length))),',
        # GuardIndex: {base + offset}, from the index of the first trap.
        'if (!seq.key().base.valid()) return __ Word32Constant(offset);',
        'uint32_t delta = offset - seq.index_offset();',
        'return delta == 0 ? index : __ Word32Add(index, __ Word32Constant(delta));',
        # CanCoalesce, Coalesce.
        'if (end_index_ < other.start_index_) return false;',
        'offsets_ = *offsets_.Hull(other.offsets_); '
        'if (other.start_index_ < start_index_) {',
        'index_ = other.index_; index_offset_ = other.index_offset_; '
        'array_length_ = other.array_length_; '
        'known_offsets_ = other.known_offsets_; '
        'non_negative_offsets_ = other.non_negative_offsets_; '
        'start_index_ = other.start_index_; '
        'start_position_ = other.start_position_; } '
        'end_index_ = other.end_index_; end_position_ = other.end_position_;',
    ],
    'cc': [
        'static constexpr uint32_t kMaxArrayLength = 1u << 30;',
        'static constexpr uint32_t kMaxReduction = 1u << 16;',
        # ProcessComparison
        'if (is_signed ? IsKnownNonNegative(key, offset) : reduction == 0 || '
        'MinLength(key.length) >= reduction) {',
        'uint64_t index_bound = key.base.valid() ? 0 : offset;',
        'RecordMinLength(key.length, index_bound + reduction + 1);',
        # ProcessNotEqual
        'uint32_t last = offset + array_length->reduction - 1;',
        'if (!known.has_value() || !known->Contains(last) || '
        'known->Contains(last + 1)) {',
        'ProcessBoundsCheck(OpIndex::Invalid(), BoundsCheck(key, last + 1), '
        'OpIndex::Invalid(), OpIndex::Invalid(), 0);',
        # ProcessBoundsCheck
        'uint32_t last = offset + reduction;',
        'if (!key.base.valid() && !(OffsetRange::IsValidRange(0, offset) && '
        'OffsetRange::IsValidRange(0, last))) {',
        'if (known.has_value() && known->Contains(offset) && '
        'known->Contains(last)) {',
        'ExtendDownToNonNegative(direct, non_negative).value_or(direct);',
        'known.has_value() ? known->Hull(checked) : checked;',
        # ExtendDownToNonNegative, KnownOffsets, NonNegativeOffsets
        '!OffsetRange::IsValidRange(non_negative->lower(), range.lower()) ||',
        '!OffsetRange::IsValidRange(non_negative->lower(), range.upper())) {',
        'return OffsetRange(non_negative->lower(), range.upper());',
        'return ExtendDownToNonNegative(*known, non_negative).value_or(*known);',
        'if (!base.valid()) return OffsetRange(0, kMaxInt);',
        # IsKnownNonNegative, RecordNonNegativeOffset, RecordMinLength
        'if (non_negative.has_value() && non_negative->Contains(offset)) '
        'return true;',
        'return known.has_value() && offset - known->upper() <= kMaxArrayLength;',
        '? known->Hull(OffsetRange(offset))',
        'if (min_length > kMaxInt) return;',
        # TryExtractArrayLength, IsArrayLengthWithoutWrapAround
        'uint32_t reduction = 0u - b.offset;',
        'if (reduction > kMaxReduction) return std::nullopt;',
        '(array_length->reduction == 0 || '
        'MinLength(LengthKey(array_length->length)) >= '
        'array_length->reduction);',
        # TryExtractNonNegativeIndex
        'uint32_t limit = relation.is_strict() ? 1u << 31 : kMaxInt;',
        'if (*bound > limit) return std::nullopt;',
        'int32_t limit = relation.is_strict() ? -1 : 0;',
        'if (static_cast<int32_t>(*bound) < limit) return std::nullopt;',
        # TryMatchInductionVariable, IsSmallBound
        'if (!init.has_value() || static_cast<int32_t>(*init) < 0) {',
        'if (step.base != value || step.offset == 0 || '
        'step.offset > kMaxArrayLength) {',
        'uint32_t limit = uint32_t{kMaxInt} - step + (inclusive ? 0 : 1);',
        '? static_cast<int32_t>(*constant) <= static_cast<int32_t>(limit)',
        ': *constant <= limit;',
        'return length.has_value() && (is_signed || length->reduction == 0);',
        # FindNotEqualBound, EntryLowerBound
        'static constexpr uint32_t kMaxUnrolledStep = 16;',
        'uint32_t all_offsets = (1u << induction.step) - 1;',
        'if (lower.has_value() && static_cast<int32_t>(induction.init) <= '
        '*lower) {',
        'if (holds && CanonicalValue(condition) == x) excluded.push_back(0);',
        'excluded.push_back(static_cast<int32_t>(*k));',
        'if (!relation->is_signed() || CanonicalValue(relation->right) != x) {',
        'static_cast<int32_t>(*k) + (relation->is_strict() ? 1 : 0);',
        'if (!lower.has_value() || bound > *lower) lower = bound;',
        'while (std::find(excluded.begin(), excluded.end(), bound) != '
        'excluded.end()) {',
        # RecordLoopBound, TryResolveMergeBound
        'if (!length.has_value() || length->reduction == 0) return;',
        'uint32_t last = length->reduction - 1;',
        'known_bounds_checks_.Set(key, OffsetRange(0, last));',
        'RecordMinLength(length_key, uint64_t{last} + 1);',
        'int64_t candidate = static_cast<int32_t>(*k + x.offset);',
        'if (candidate < bound.x_lower_bound) continue;',
        'ReducedLength length{input.base_value, 0u - (input.offset + x.offset)};',
        'if (length.reduction > kMaxReduction) return std::nullopt;',
        # Constants as lengths: TryExtractArrayLength, MinLength,
        # KnownOffsets.
        'if (b.offset >= kMaxArrayLength) return std::nullopt;',
        'OffsetRange below_min_length(0, min_length - 1);',
        'known = known.has_value() ? known->Hull(below_min_length).value_or(*known)',
        # TryExtractBoundsCheckCondition: non-strict comparisons.
        'if (reduction >= 1 && (relation.is_signed() || '
        'MinLength(length_key) >= reduction)) { reduction--;',
        '(relation.is_signed() ? static_cast<int32_t>(offset) >= 1 '
        ': offset >= 1)) { offset--;',
        # ProcessNotEqualToConstant.
        'uint64_t excluded = uint64_t{n} + length.reduction;',
        'if (excluded != MinLength(length_key)) return;',
        'RecordMinLength(length_key, excluded + 1);',
        'ProcessNotEqualToConstant(*length, 0);',
        # ProcessDecreasingInduction, HasDecreasingLowerBound.
        'uint32_t decrement = 0u - step.offset;',
        'if (step.base != value || decrement == 0 || '
        'decrement > kMaxArrayLength) {',
        # (The entry lower bound is computed lazily since bce-series-v2.)
        'std::optional<int64_t> lower = init_lower(); '
        'if (!lower.has_value() || *lower < 0) return;',
        'uint32_t v = k - n; if (v <= kMaxInt) excluded.push_back(v);',
        'if (d > 0 || d < -int64_t{kMaxArrayLength}) continue;',
        'int64_t lower = static_cast<int32_t>(*lo) + '
        '(relation.is_strict() ? 1 : 0); if (lower - d >= decrement) return true;',
        'std::optional<int64_t> lower = init_lower(); '
        'if (!lower.has_value() || y > *lower) continue;',
        # EntryLowerBoundOfStart.
        'if (bound >= 0 && (!lower.has_value() || bound > *lower)) lower = bound;',
        'raise(int64_t{MinLength(LengthKey(length->length))} - length->reduction);',
        'o = -int64_t{static_cast<int32_t>(*constant)};',
        'if (o >= 0 || o < -int64_t{kMaxArrayLength}) return lower;',
        'raise(*x_lower + o);',
        # DecomposeIndex: truncated additions.
        'offset += op->kind == WordBinopOp::Kind::kAdd ? *constant : -*constant;',
        # Normalize: narrowing (7c94e0ee3b6).
        'if (relation.kind != Kind::kUnsignedLessThan && '
        'relation.kind != Kind::kUnsignedLessThanOrEqual) { return std::nullopt;',
        '.TryCast<Opmask::kChangeUint32ToUint64>(); '
        'if (zext == nullptr) return std::nullopt;',
        'return Relation{relation.kind, /*not_equal=*/false, relation.left, '
        'zext->input(), /*narrowed=*/true};',
        'reduction == 0 && !relation->narrowed;',
        # DecomposeIndex: 64-bit values read as their truncations.
        'change && (change->Is<Opmask::kChangeUint32ToUint64>() || '
        'change->Is<Opmask::kChangeInt32ToInt64>())) {',
        'binop->kind == WordBinopOp::Kind::kAdd ? *constant : -*constant;',
        'return {OpIndex::Invalid(), TruncationKey(index), offset};',
        # UpdateKnownBoundsChecks, RecordFallbackSequence.
        'OpIndex start_index = starts_at_condition ? condition : trap_if;',
        'TrapInfo{trap_if, index, length, start_index, start_position, '
        'known_before, non_negative_before});',
        'OffsetRange(previous_offset).Hull(OffsetRange(offset));',
        'OpIndex fallback_end_index = graph_.NextIndex(trap_if);',
        'FallbackInstructionSequence new_sequence( phase_zone_, key, '
        'previous.index, previous_offset, previous.length, *offsets, '
        'previous.known_offsets, previous.non_negative_offsets, '
        'previous.start_index, fallback_end_index, previous.start_position, '
        'current_position_ + 1, {previous.trap_if, trap_if});',
    ],
}


def check_anchors():
    ok = True
    for ext, anchors in ANCHORS.items():
        text = ''.join(open(os.path.join(V8, f'{SRC}.{ext}')).read().split())
        for anchor in anchors:
            if ''.join(anchor.split()) not in text:
                print(f'MISSING in .{ext}: {anchor}')
                ok = False
    return ok


def bv(n):
    return BitVecVal(n % 2**32, 32)


def bv64(n):
    return BitVecVal(n % 2**64, 64)


K_MAX_INT = 2**31 - 1
K_MAX_ARRAY_LENGTH = 1 << 30
K_MAX_REDUCTION = 1 << 16
K_MAX_UNROLLED_STEP = 16

counter = [0]


def fresh(name, bits=32):
    counter[0] += 1
    return BitVec(f'{name}{counter[0]}', bits)


def fresh_bool(name):
    counter[0] += 1
    return Bool(f'{name}{counter[0]}')


# OffsetRange.
def valid_range(lower, upper):
    return (upper - lower) >= 0


class Opt:
    """An optional range: {present}, then [lo, hi]."""
    def __init__(self, present, lo, hi):
        self.present, self.lo, self.hi = present, lo, hi

    @staticmethod
    def sym(name):
        return Opt(fresh_bool(f'{name}_present'), fresh(f'{name}_lo'),
                   fresh(f'{name}_hi'))

    @staticmethod
    def some(lo, hi):
        return Opt(BoolVal(True), lo, hi)


def classify(r, offset):
    inside = And(valid_range(r.lo, offset), valid_range(offset, r.hi))
    above = And(Not(inside), valid_range(r.hi, offset),
                valid_range(r.lo, offset))
    below = And(Not(inside), Not(above), valid_range(offset, r.lo),
                valid_range(offset, r.hi))
    return inside, above, below


def contains(r, offset):
    return And(r.present, classify(r, offset)[0])


def hull(a, b):
    # Both present.
    present, lo, hi = BoolVal(False), bv(0), bv(0)
    for first, second in [(a, b), (b, a)]:
        second_lower = second.lo - first.lo
        second_upper = second.hi - first.lo
        size = If(UGT(first.hi - first.lo, second_upper), first.hi - first.lo,
                  second_upper)
        ok = And(Not(UGT(second_lower, second_upper)), size >= 0)
        take = And(ok, Or(Not(present), ULT(size, hi - lo)))
        lo, hi = If(take, first.lo, lo), If(take, first.lo + size, hi)
        present = Or(present, take)
    return Opt(present, lo, hi)


def hull_opt(a, b):
    # {a} may be absent, {b} is present.
    h = hull(a, b)
    return Opt(If(a.present, h.present, True), If(a.present, h.lo, b.lo),
               If(a.present, h.hi, b.hi))


def extend_down(r, non_negative):
    present = And(r.present, non_negative.present,
                  valid_range(non_negative.lo, r.lo),
                  valid_range(non_negative.lo, r.hi))
    return Opt(present, non_negative.lo, r.hi)


def value_or(a, b):
    return Opt(Or(a.present, b.present), If(a.present, a.lo, b.lo),
               If(a.present, a.hi, b.hi))


def known_offsets(known, non_negative):
    e = extend_down(known, non_negative)
    return Opt(known.present, If(e.present, e.lo, known.lo),
               If(e.present, e.hi, known.hi))


def with_min_length(known, m):
    # For a constant index, the hull of {known} with the offsets below the
    # min length {m}, if {m > 0} ([min-length-constant-index]), or {known}
    # if there is no hull.
    below = Opt.some(bv(0), m - 1)
    h = hull(known, below)
    return Opt(Or(known.present, m != 0),
               If(m == 0, known.lo,
                  If(known.present, If(h.present, h.lo, known.lo), bv(0))),
               If(m == 0, known.hi,
                  If(known.present, If(h.present, h.hi, known.hi), m - 1)))


def constant_non_negative():
    return Opt.some(bv(0), bv(K_MAX_INT))


def is_known_non_negative(base_valid, known, non_negative, offset):
    if not base_valid:
        return contains(constant_non_negative(), offset)
    return Or(contains(non_negative, offset),
              And(known.present,
                  ULE(offset - known.hi, bv(K_MAX_ARRAY_LENGTH))))


# Facts.
# Array lengths, and constants used as lengths ([constant-length]), are
# less than 2^30.
def env(l):
    return [l >= 0, ULT(l, bv(K_MAX_ARRAY_LENGTH))]


def in_bounds(r, x, l):
    return Implies(r.present, And(valid_range(r.lo, r.hi), ULT(x + r.lo, l),
                                  ULT(x + r.hi, l)))


def non_negative_fact(r, x):
    return Implies(r.present, And(valid_range(r.lo, r.hi), x + r.lo >= 0,
                                  x + r.hi >= 0))


def in_bounds_violated(r, x, l):
    k = fresh('k')
    return And(r.present, Or(Not(valid_range(r.lo, r.hi)),
                             And(contains(r, k), UGE(x + k, l))))


def non_negative_violated(r, x):
    k = fresh('k')
    return And(r.present, Or(Not(valid_range(r.lo, r.hi)),
                             And(contains(r, k), x + k < 0)))


results = []
started = [START is None]


def skipped(name):
    # With --from, the queries before the first one whose name contains it.
    if not started[0]:
        if START not in name: return True
        started[0] = True
    return False


def prove(name, assumptions, violation):
    if skipped(name): return
    start = time.time()
    # The solver for quantifier-free bitvector formulas is much faster
    # than the default one on these queries, and so is a fresh solver
    # than an incremental one.
    s = SolverFor('QF_BV')
    s.add(*assumptions)
    vacuous = s.check() != sat
    s = SolverFor('QF_BV')
    s.add(*assumptions, violation)
    r = s.check()
    ok = r == unsat and not vacuous
    results.append(ok)
    status = 'ok' if ok else ('VACUOUS' if vacuous else f'FAILS ({r})')
    print(f'{status:8} {name} ({time.time() - start:.1f} s)', flush=True)
    if r == sat:
        print('         counterexample:', s.model())


# The state before a step, for a base {x} (or a constant index, with
# {x} = 0 and the non-negative offsets [0, kMaxInt]).
class State:
    def __init__(self, base_valid):
        self.base_valid = base_valid
        self.x = fresh('x') if base_valid else bv(0)
        self.l = fresh('l')
        self.known = Opt.sym('known')
        self.non_negative = (Opt.sym('nn') if base_valid
                             else constant_non_negative())
        self.min_length = fresh('min_length')

    def facts(self):
        return [*env(self.l), in_bounds(self.known, self.x, self.l),
                non_negative_fact(self.non_negative, self.x),
                UGE(self.l, self.min_length)]

    def known_offsets(self):
        # KnownOffsets: for a constant index, the min length also gives
        # offsets within bounds.
        known = (self.known if self.base_valid
                 else with_min_length(self.known, self.min_length))
        return known_offsets(known, self.non_negative)


BASES = [(True, 'base'), (False, 'constant')]


def check_ranges():
    for base_valid, what in BASES:
        st = State(base_valid)
        r = Opt.sym('r')
        prove(f'[range-endpoints] in bounds ({what})',
              [*env(st.l), in_bounds(r, st.x, st.l)],
              in_bounds_violated(r, st.x, st.l))
        prove(f'[range-endpoints] non-negative ({what})',
              [non_negative_fact(r, st.x)], non_negative_violated(r, st.x))
    x, l = fresh('x'), fresh('l')
    a, b = Opt.sym('a'), Opt.sym('b')
    h = hull(a, b)
    prove('Hull of ranges within bounds',
          [*env(l), a.present, b.present, in_bounds(a, x, l),
           in_bounds(b, x, l), h.present], in_bounds_violated(h, x, l))
    prove('Hull of non-negative ranges (RecordNonNegativeOffset)',
          [a.present, b.present, non_negative_fact(a, x),
           non_negative_fact(b, x), h.present], non_negative_violated(h, x))
    prove('Hull contains both ranges',
          [a.present, b.present, valid_range(a.lo, a.hi),
           valid_range(b.lo, b.hi), h.present],
          Not(And(contains(h, a.lo), contains(h, a.hi), contains(h, b.lo),
                  contains(h, b.hi))))
    for base_valid, what in BASES:
        st = State(base_valid)
        prove(f'KnownOffsets ({what})', st.facts(),
              in_bounds_violated(st.known_offsets(), st.x, st.l))
        offset = fresh('offset')
        prove(f'IsKnownNonNegative ({what})',
              [*st.facts(),
               is_known_non_negative(base_valid, st.known, st.non_negative,
                                     offset)],
              (st.x + offset) < 0)


def process_bounds_check(st, offset, reduction):
    """Returns (redundant, new known range, recorded) for ProcessBoundsCheck."""
    last = offset + reduction
    early = (BoolVal(False) if st.base_valid
             else Not(And(valid_range(bv(0), offset), valid_range(bv(0), last))))
    known = st.known_offsets()
    redundant = And(Not(early), known.present, contains(known, offset),
                    contains(known, last))
    direct = Opt.some(offset, last)
    checked = value_or(extend_down(direct, st.non_negative), direct)
    offsets = hull_opt(known, checked)
    recorded = And(Not(early), Not(redundant), offsets.present)
    return redundant, offsets, recorded, last


def check_process_comparison():
    for base_valid, what in BASES:
        for is_signed in [False, True]:
            st = State(base_valid)
            offset, reduction = fresh('offset'), fresh('reduction')
            index = st.x + offset
            length = st.l - reduction
            # TryExtractArrayLength.
            assumptions = [*st.facts(), ULE(reduction, bv(K_MAX_REDUCTION))]
            if is_signed:
                gate = is_known_non_negative(base_valid, st.known,
                                             st.non_negative, offset)
                condition = index < length
            else:
                gate = Or(reduction == 0, UGE(st.min_length, reduction))
                condition = ULT(index, length)
            redundant, offsets, recorded, last = process_bounds_check(
                st, offset, reduction)
            kind = f'{"signed" if is_signed else "unsigned"}, {what}'
            prove(f'ProcessBoundsCheck: direct range is valid ({kind})',
                  assumptions, Not(valid_range(offset, last)))
            prove(f'ProcessComparison: new range within bounds ({kind})',
                  [*assumptions, gate, condition, recorded],
                  in_bounds_violated(offsets, st.x, st.l))
            # RecordMinLength(index_bound + reduction + 1), if at most kMaxInt.
            index_bound = (bv64(0) if base_valid else ZeroExt(32, offset))
            min_length = index_bound + ZeroExt(32, reduction) + 1
            prove(f'ProcessComparison: min length ({kind})',
                  [*assumptions, gate, condition,
                   ULE(index_bound, bv64(K_MAX_INT)),
                   ULE(min_length, bv64(K_MAX_INT))],
                  ULT(ZeroExt(32, st.l), min_length))
        st = State(base_valid)
        offset = fresh('offset')
        redundant, _, _, _ = process_bounds_check(st, offset, bv(0))
        prove(f'ProcessBoundsCheck: redundant trap cannot fail ({what})',
              [*st.facts(), redundant], UGE(st.x + offset, st.l))


def check_process_not_equal():
    for base_valid, what in BASES:
        st = State(base_valid)
        offset, reduction = fresh('offset'), fresh('reduction')
        last = offset + reduction - 1
        known = st.known_offsets()
        prove(f'ProcessNotEqual ({what})',
              [*st.facts(), ULE(reduction, bv(K_MAX_REDUCTION)),
               st.x + offset != st.l - reduction,
               contains(known, last), Not(contains(known, last + 1))],
              UGE(st.x + last + 1, st.l))


def check_non_negative_index():
    for base_valid, what in BASES:
        st = State(base_valid)
        offset, bound, reduction = fresh('offset'), fresh('b'), fresh('r')
        index = st.x + offset
        for strict in [True, False]:
            op = ULT if strict else ULE
            # The bound is a reduced length without wrap around.
            prove(f'TryExtractNonNegativeIndex: x {"<u" if strict else "<=u"} '
                  f'length ({what})',
                  [*st.facts(), ULE(reduction, bv(K_MAX_REDUCTION)),
                   Or(reduction == 0, UGE(st.min_length, reduction)),
                   op(index, st.l - reduction)], index < 0)
            limit = bv(1 << 31) if strict else bv(K_MAX_INT)
            prove(f'TryExtractNonNegativeIndex: x {"<u" if strict else "<=u"} '
                  f'constant ({what})',
                  [ULE(bound, limit), op(index, bound)], index < 0)
            limit = bv(-1) if strict else bv(0)
            sop = (lambda a, b: a < b) if strict else (lambda a, b: a <= b)
            prove(f'TryExtractNonNegativeIndex: constant {"<s" if strict else "<=s"}'
                  f' x ({what})',
                  [bound >= limit, sop(bound, index)], index < 0)


def guard_index(base_valid, index, index_offset, offset):
    # GuardIndex: {base + offset}, from the index of the first trap of the
    # sequence, {base + index_offset}.
    if not base_valid:
        return offset
    delta = offset - index_offset
    return If(delta == 0, index, index + delta)


def guard(base_valid, index, index_offset, length, offsets, known, nn):
    """Returns (check_lower, check_upper, passes, at) for the guard of a
    sequence (ComputeGuard, EmitBoundsCheck), with {passes} for a guard
    checking each bound separately, and {at(offset)} the index it
    checks for {offset}."""
    lo, hi = offsets.lo, offsets.hi

    def implies_lower(facts):
        inside, above, _ = classify(facts, lo)
        return And(facts.present,
                   Or(inside, And(above, valid_range(facts.hi, hi))))

    def implies_upper(k):
        inside, _, below = classify(k, hi)
        return And(k.present,
                   Or(inside, And(below, valid_range(lo, k.lo))))

    lower_implied = Or(implies_lower(known), implies_lower(nn))
    upper_implied = implies_upper(known)
    check_lower = Not(lower_implied)
    check_upper = Or(lower_implied, Not(upper_implied))
    at = lambda offset: guard_index(base_valid, index, index_offset, offset)
    one_sided = And(Implies(check_upper, ULT(at(hi), length)),
                    Implies(check_lower, ULT(at(lo), length)))
    return check_lower, check_upper, one_sided, at


def check_guards():
    # The guard of a sequence is computed from the index {index} of its
    # first trap, which is {x + index_offset}, and from the length of that
    # trap: this is what the invariant of sequences states (see
    # check_fallback_sequences), for the values of {x} and {l} at the start
    # of the sequence, which are their values at its covered traps
    # (Canonical.guard_value_persists).
    for base_valid, what in BASES:
        for single in [True, False]:
            st = State(base_valid)
            lo, hi, io = fresh('lo'), fresh('hi'), fresh('index_offset')
            offsets = Opt.some(lo, hi)
            x, l = st.x, st.l
            index = x + io
            check_lower, check_upper, one_sided, at = guard(
                base_valid, index, io, l, offsets, st.known_offsets(),
                st.non_negative)
            if single:
                # EmitTwoSidedBoundsCheck, on 64 bits.
                two_sided = ULT(ZeroExt(32, at(lo)) + ZeroExt(32, hi - lo),
                                ZeroExt(32, l))
                passes = If(And(check_lower, check_upper), two_sided,
                            one_sided)
            else:
                passes = one_sided
            bits = "64" if single else "32"
            prove(f'Guard of a fallback sequence ({what}, {bits}-bit)',
                  [*st.facts(), valid_range(lo, hi), passes],
                  in_bounds_violated(offsets, x, l))
            # When the guard fails, one of the bounds of the range is out
            # of bounds. These are offsets of covered traps, which are in
            # the fallback code: one of them traps before its Unreachable.
            prove(f'Failing guard: a bound is out of bounds ({what}, '
                  f'{bits}-bit)',
                  [*env(l), valid_range(lo, hi), Not(passes)],
                  And(ULT(x + lo, l), ULT(x + hi, l)))


# Fallback sequences. Positions are those of the operations of the block
# (and of its dominators, before it), in order. A sequence covers the
# traps of a range of positions [start, end). Its fields are those of
# FallbackInstructionSequence, with the positions where its index and its
# length are defined, the positions where its known and non-negative
# offsets were known, and the positions of the covered traps whose
# offsets are the bounds of its range.
class Seq:
    def __init__(self, name):
        f = lambda field: fresh(f'{name}_{field}')
        self.start, self.end = f('start'), f('end')
        self.index, self.index_offset, self.length = (
            f('index'), f('index_offset'), f('length'))
        self.index_pos, self.length_pos = f('index_pos'), f('length_pos')
        self.offsets = Opt.some(f('lo'), f('hi'))
        self.known, self.nn = Opt.sym(f'{name}_known'), Opt.sym(f'{name}_nn')
        self.known_at, self.nn_at = f('known_at'), f('nn_at')
        self.lo_trap, self.hi_trap = f('lo_trap'), f('hi_trap')

    def covers(self, pos):
        return And(ULE(self.start, pos), ULT(pos, self.end))

    def invariant(self, base_valid, x, l):
        # What the guard needs, for the values {x} of the base and {l} of
        # the length at the start, which are their values at the covered
        # traps (Canonical.guard_value_persists).
        return [
            # The guard's operands are computed before the sequence...
            ULT(self.index_pos, self.start), ULT(self.length_pos, self.start),
            # ... and are the index {x + index_offset} and the length of a
            # trap (only the length for a constant index).
            self.index == x + self.index_offset if base_valid else BoolVal(True),
            self.length == l,
            valid_range(self.offsets.lo, self.offsets.hi),
            # The facts are those known at the start.
            self.known_at == self.start, self.nn_at == self.start,
            # The bounds of the range are offsets of covered traps, which
            # the fallback code checks when the guard fails.
            self.covers(self.lo_trap), self.covers(self.hi_trap)]


def coalesce(a, b):
    """Returns ({b} merged into {a}, the hull exists) for Coalesce."""
    r = Seq('merged')
    h = hull(a.offsets, b.offsets)
    move = ULT(b.start, a.start)
    pick = lambda fa, fb: If(move, fb, fa)
    r.index, r.index_offset = pick(a.index, b.index), pick(a.index_offset,
                                                            b.index_offset)
    r.index_pos = pick(a.index_pos, b.index_pos)
    r.length, r.length_pos = pick(a.length, b.length), pick(a.length_pos,
                                                             b.length_pos)
    r.known = Opt(pick(a.known.present, b.known.present),
                  pick(a.known.lo, b.known.lo), pick(a.known.hi, b.known.hi))
    r.known_at = pick(a.known_at, b.known_at)
    r.nn = Opt(pick(a.nn.present, b.nn.present), pick(a.nn.lo, b.nn.lo),
               pick(a.nn.hi, b.nn.hi))
    r.nn_at = pick(a.nn_at, b.nn_at)
    r.start = pick(a.start, b.start)
    r.end = b.end
    r.offsets = Opt.some(h.lo, h.hi)
    # The covered traps are those of both sequences. The bound of the
    # merged range must be a bound of one of the ranges (otherwise, no
    # covered trap is known to have it: position {r.end}, outside).
    bound_trap = lambda v, va, vb, ta, tb: If(v == va, ta, If(v == vb, tb, r.end))
    r.lo_trap = bound_trap(h.lo, a.offsets.lo, b.offsets.lo, a.lo_trap, b.lo_trap)
    r.hi_trap = bound_trap(h.hi, a.offsets.hi, b.offsets.hi, a.hi_trap, b.hi_trap)
    return r, h.present


def check_fallback_sequences():
    for base_valid, what in BASES:
        x = fresh('x') if base_valid else bv(0)
        l = fresh('l')
        # RecordFallbackSequence, from the previous trap of the key (its
        # TrapInfo) and the current one. The index and the length of the
        # previous trap are inputs of its condition, which precedes it; the
        # sequence starts at the condition if it is right before the trap.
        # Its known and non-negative offsets are those known when the
        # previous trap was processed, which are those known at its
        # condition (nothing is recorded in between).
        cond, prev, cur = fresh('cond'), fresh('prev_trap'), fresh('cur_trap')
        prev_offset, offset = fresh('prev_offset'), fresh('offset')
        at_condition = fresh_bool('starts_at_condition')
        s = Seq('new')
        h = hull(Opt.some(prev_offset, prev_offset), Opt.some(offset, offset))
        structure = [ULT(cond, prev), ULT(prev, cur), ULT(cur, cur + 1),
                     ULT(s.index_pos, cond), ULT(s.length_pos, cond)]
        s.start = If(at_condition, cond, prev)
        s.end = cur + 1
        s.index = x + prev_offset
        s.index_offset = prev_offset
        s.length = l
        s.known_at, s.nn_at = s.start, s.start
        s.offsets = Opt.some(h.lo, h.hi)
        bound_trap = lambda v: If(v == prev_offset, prev,
                                  If(v == offset, cur, s.end))
        s.lo_trap, s.hi_trap = bound_trap(h.lo), bound_trap(h.hi)
        prove(f'RecordFallbackSequence: invariant ({what})',
              [*structure, h.present], Not(And(*s.invariant(base_valid, x, l))))
        # Coalesce: {b} ends after {a} (DCHECK), and they overlap or are
        # adjacent (CanCoalesce), so that the merged range covers both.
        # The hull exists (W9).
        a, b = Seq('a'), Seq('b')
        r, present = coalesce(a, b)
        # Any other covered trap of either sequence.
        ta, tb, oa, ob = fresh('a_trap'), fresh('b_trap'), fresh('oa'), fresh('ob')
        prove(f'Coalesce: invariant ({what})',
              [*a.invariant(base_valid, x, l), *b.invariant(base_valid, x, l),
               ULE(a.end, b.end), Not(ULT(a.end, b.start)), present,
               a.covers(ta), contains(a.offsets, oa),
               b.covers(tb), contains(b.offsets, ob)],
              Not(And(*r.invariant(base_valid, x, l),
                      r.covers(ta), contains(r.offsets, oa),
                      r.covers(tb), contains(r.offsets, ob))))


def check_small_bound():
    for is_signed in [False, True]:
        for inclusive in [False, True]:
            i, c, step = fresh('i'), fresh('c'), fresh('step')
            limit = bv(K_MAX_INT) - step + (0 if inclusive else 1)
            small = (c <= limit) if is_signed else ULE(c, limit)
            if is_signed:
                relation = (i <= c) if inclusive else (i < c)
            else:
                relation = ULE(i, c) if inclusive else ULT(i, c)
            # TryMatchInductionVariable.
            step_ok = [step != 0, ULE(step, bv(K_MAX_ARRAY_LENGTH))]
            kind = (f'{"signed" if is_signed else "unsigned"}, '
                    f'{"inclusive" if inclusive else "strict"}')
            prove(f'IsSmallBound: constant ({kind})',
                  [i >= 0, *step_ok, small, relation], (i + step) < 0)
            l, r = fresh('l'), fresh('r')
            x = l - r
            if is_signed:
                relation = (i <= x) if inclusive else (i < x)
            else:
                relation = ULE(i, x) if inclusive else ULT(i, x)
            prove(f'IsSmallBound: length ({kind})',
                  [*env(l), ULE(r, bv(K_MAX_REDUCTION)), i >= 0, *step_ok,
                   BoolVal(True) if is_signed else r == 0, relation],
                  (i + step) < 0)


def entry_lower_bound(x, n_lower, n_excluded, x_constant):
    """Returns (assumptions, lower bound present, lower bound) for
    EntryLowerBound, with {n_lower} conditions {k <= x} or {k < x}
    (signed), and {n_excluded} values {x} differs from."""
    assumptions = []
    present = BoolVal(x_constant)
    lower = SignExt(32, x)
    for _ in range(n_lower):
        k, strict, used = fresh('k'), fresh_bool('strict'), fresh_bool('used')
        assumptions.append(Implies(used, If(strict, k < x, k <= x)))
        bound = SignExt(32, k) + If(strict, bv64(1), bv64(0))
        take = And(used, Or(Not(present), bound > lower))
        lower = If(take, bound, lower)
        present = Or(present, used)
    excluded = []
    for _ in range(n_excluded):
        e, used = fresh('e'), fresh_bool('used')
        assumptions.append(Implies(used, x != e))
        excluded.append((used, SignExt(32, e)))
    # The loop increments the bound at most once per excluded value.
    for _ in range(n_excluded):
        hit = Or(*[And(used, lower == e) for used, e in excluded])
        lower = If(hit, lower + 1, lower)
    return assumptions, present, lower


def check_not_equal_induction():
    # Two conditions and three excluded values: with more, the same
    # invariant ({x} is at least {lower}) is kept by each step.
    for x_constant in [False, True]:
        x = fresh('x')
        assumptions, present, lower = entry_lower_bound(x, 2, 3, x_constant)
        prove(f'EntryLowerBound ({"constant" if x_constant else "value"})',
              [*assumptions, present], SignExt(32, x) < lower)
    # FindNotEqualBound: {init <= lower}, with {init >= 0}
    # (TryMatchInductionVariable), and [induction-not-equal] for each step.
    for step in range(1, K_MAX_UNROLLED_STEP + 1):
        i, x = fresh('i'), fresh('x')
        prove(f'Not-equal induction, step {step}',
              [i >= 0, i <= x, *[i + k != x for k in range(step)]],
              Not(And(i + step >= 0, i + step <= x)))


def check_loop_bound():
    i, l, r = fresh('i'), fresh('l'), fresh('r')
    k = fresh('k')
    last = r - 1
    known = Opt.some(bv(0), last)
    assumptions = [*env(l), r != 0, ULE(r, bv(K_MAX_REDUCTION)), i >= 0,
                   i <= l - r]
    prove('RecordLoopBound: offsets [0, r - 1] within bounds', assumptions,
          in_bounds_violated(known, i, l))
    prove('RecordLoopBound: min length', assumptions,
          ULT(ZeroExt(32, l), ZeroExt(32, last) + 1))


def check_merge_bound():
    phi, offset, k = fresh('phi'), fresh('offset'), fresh('k')
    lower = fresh('lower', 64)
    x = phi + offset
    candidate = SignExt(32, k + offset)
    prove('TryResolveMergeBound: ruled-out constants',
          [SignExt(32, x) >= lower, phi == k], candidate < lower)
    length, input_offset = fresh('length'), fresh('input_offset')
    reduction = 0 - (input_offset + offset)
    prove('TryResolveMergeBound: alias',
          [phi == length + input_offset, ULE(reduction, bv(K_MAX_REDUCTION))],
          x != length - reduction)


# bce-loop-ideas: non-strict comparisons, constants as lengths, not-equal
# to a constant, decreasing loops, and truncated additions.


def check_non_strict():
    # TryExtractBoundsCheckCondition rewrites {x <= l - r} as
    # {x < l - (r - 1)} when {r >= 1} (and {l - r} does not wrap around
    # for an unsigned comparison), and {n <= l - r} as {n - 1 < l - r} for
    # a constant {n >= 1}. The rewritten condition is then processed as
    # any other (see check_process_comparison).
    for is_signed in [False, True]:
        kind = 'signed' if is_signed else 'unsigned'
        le = (lambda a, b: a <= b) if is_signed else ULE
        lt = (lambda a, b: a < b) if is_signed else ULT
        index, l, r, m = fresh('index'), fresh('l'), fresh('r'), fresh('m')
        prove(f'Non-strict comparison with a reduced length ({kind})',
              [*env(l), UGE(l, m), ULE(r, bv(K_MAX_REDUCTION)), r != 0,
               BoolVal(True) if is_signed else UGE(m, r), le(index, l - r)],
              Not(lt(index, l - (r - 1))))
        n = fresh('n')
        prove(f'Non-strict comparison with a constant index ({kind})',
              [*env(l), ULE(r, bv(K_MAX_REDUCTION)),
               (n >= 1) if is_signed else UGE(n, 1), le(n, l - r)],
              Not(lt(n - 1, l - r)))


def check_not_equal_to_constant():
    # ProcessNotEqualToConstant: {l - r != n}, with {l} at least
    # {n + r} (exactly), shows that {l} is at least {n + r + 1}. A value
    # that holds is {l - r != 0}.
    l, r, n, m = fresh('l'), fresh('r'), fresh('n'), fresh('m')
    excluded = ZeroExt(32, n) + ZeroExt(32, r)
    prove('ProcessNotEqualToConstant',
          [*env(l), UGE(l, m), ULE(m, bv(K_MAX_INT)),
           ULE(r, bv(K_MAX_REDUCTION)), excluded == ZeroExt(32, m),
           l - r != n],
          ULT(ZeroExt(32, l), excluded + 1))


def check_decreasing_induction():
    # HasDecreasingLowerBound, first case: {lo <= i + d} (or {lo < i + d}),
    # signed, with {-2^30 <= d <= 0} and {lo (+ 1) - d >= c}, shows that
    # {i - c} is non-negative ([induction-decreasing]).
    i, lo, d32, c = fresh('i'), fresh('lo'), fresh('d'), fresh('c')
    strict = fresh_bool('strict')
    d = SignExt(32, d32)
    lower = SignExt(32, lo) + If(strict, bv64(1), bv64(0))
    prove('HasDecreasingLowerBound: lo <= i + d',
          [i >= 0, c != 0, ULE(c, bv(K_MAX_ARRAY_LENGTH)),
           d <= 0, d >= -K_MAX_ARRAY_LENGTH,
           If(strict, lo < i + d32, lo <= i + d32),
           lower - d >= ZeroExt(32, c)],
          (i - c) < 0)
    # Second case: {i + n != k} is {i != k - n}, and when {i != y + k}
    # for all {k} below the step {c}, with {y <= i}, {i - c} is at least
    # {y} ([induction-decreasing-not-equal]). {y} is at most kMaxInt.
    i, n, k = fresh('i'), fresh('n'), fresh('k')
    prove('HasDecreasingLowerBound: i + n != k is i != k - n',
          [], (i + n != k) != (i != k - n))
    for step in range(1, K_MAX_UNROLLED_STEP + 1):
        i, y = fresh('i'), fresh('y')
        prove(f'HasDecreasingLowerBound: not-equal, step {step}',
              [i >= 0, y >= 0, i >= y, *[i != y + k for k in range(step)]],
              Not(And(i - step >= 0, i - step >= y)))
    # EntryLowerBoundOfStart: {init = l - r}, with {l} at least {m} and
    # {m - r >= 0}, is at least {m - r}; {init = x + o}, with
    # {-2^30 <= o < 0} and {x} at least {x_lower}, with
    # {x_lower + o >= 0}, is at least {x_lower + o}
    # ([entry-lower-bound-offset]).
    l, r, m = fresh('l'), fresh('r'), fresh('m')
    bound = ZeroExt(32, m) - ZeroExt(32, r)
    prove('EntryLowerBoundOfStart: reduced length',
          [*env(l), UGE(l, m), ULE(r, bv(K_MAX_REDUCTION)), bound >= 0],
          SignExt(32, l - r) < bound)
    x, o32, x_lower = fresh('x'), fresh('o'), fresh('x_lower', 64)
    o = SignExt(32, o32)
    # {x_lower} comes from EntryLowerBound: a 32-bit constant, plus 1 for
    # a strict comparison and for each excluded value.
    prove('EntryLowerBoundOfStart: offset',
          [o < 0, o >= -K_MAX_ARRAY_LENGTH, SignExt(32, x) >= x_lower,
           x_lower >= -2**31, x_lower <= 2**32, x_lower + o >= 0],
          SignExt(32, x + o32) < x_lower + o)


def check_truncated_addition():
    # DecomposeIndex: {trunc(x + c)} is {trunc(x) + trunc(c)}, and
    # {trunc(x - c)} is {trunc(x) - trunc(c)} ([truncated-addition]).
    x, c = fresh('x', 64), fresh('c', 64)
    low = lambda v: Extract(31, 0, v)
    prove('Truncated addition', [], low(x + c) != low(x) + low(c))
    prove('Truncated subtraction', [], low(x - c) != low(x) - low(c))


# Well-formedness: what the analysis builds must be valid whatever the
# facts, including in unreachable code, where facts may contradict each
# other. These queries only assume what holds by construction (valid
# input ranges, the limits checked by the code), not that facts hold.
# Each OffsetRange the code builds must be valid (its constructor
# DCHECKs it), and the DCHECKs on values must hold.


def valid_opt(r):
    return Implies(r.present, valid_range(r.lo, r.hi))


def check_well_formedness():
    a, b = Opt.sym('a'), Opt.sym('b')
    h = hull(a, b)
    prove('W1 Hull is valid',
          [a.present, b.present, valid_range(a.lo, a.hi),
           valid_range(b.lo, b.hi)],
          Not(valid_opt(h)))
    r, nn = Opt.sym('r'), Opt.sym('nn')
    prove('W2 ExtendDownToNonNegative is valid',
          [r.present, valid_range(r.lo, r.hi), valid_opt(nn)],
          Not(valid_opt(extend_down(r, nn))))
    # Reductions come from TryExtractArrayLength or TryResolveMergeBound
    # (at most kMaxReduction), possibly minus 1 (non-strict comparisons),
    # or are 0 (ProcessNotEqual).
    offset, reduction = fresh('offset'), fresh('reduction')
    prove('W3 ProcessBoundsCheck: direct range',
          [ULE(reduction, bv(K_MAX_REDUCTION))],
          Not(valid_range(offset, offset + reduction)))
    # The min length is what MinLength returns for the key of the array
    # (see min_length_model), not assumed to be bounded.
    known, nn = Opt.sym('known'), Opt.sym('nn')
    m_assumptions, m = min_length_model()
    prove('W4 KnownOffsets with a min length (constant index)',
          [*m_assumptions, valid_opt(known), valid_opt(nn), m != 0],
          Or(Not(valid_range(bv(0), m - 1)),
             Not(valid_opt(known_offsets(with_min_length(known, m), nn)))))
    r = fresh('r')
    prove('W5 RecordLoopBound: [0, r - 1]',
          [r != 0, ULE(r, bv(K_MAX_REDUCTION))],
          Not(valid_range(bv(0), r - 1)))
    # ProcessBoundsCheck for a trap (reduction 0): the offset is not in
    # {known} (otherwise the trap is redundant), and the hull of {known}
    # and {checked} (the offset, possibly extended down) exists, so the
    # offset is above or below {known}.
    known, nn, offset = Opt.sym('known'), Opt.sym('nn'), fresh('offset')
    direct = Opt.some(offset, offset)
    checked = value_or(extend_down(direct, nn), direct)
    h = hull(known, checked)
    inside, above, below = classify(known, offset)
    prove('W6 ProcessBoundsCheck: the trap is above or below',
          [known.present, valid_range(known.lo, known.hi), valid_opt(nn),
           Not(inside), h.present],
          Not(Or(above, below)))
    # RecordFallbackSequence: the previous trap's offset is the bound of
    # {known} on the side of the offset, so their hull exists.
    prev = If(above, known.hi, known.lo)
    h2 = hull(Opt.some(prev, prev), Opt.some(offset, offset))
    prove('W7 RecordFallbackSequence: the hull of the two traps exists',
          [known.present, valid_range(known.lo, known.hi), Or(above, below)],
          Not(h2.present))
    check_min_length_keys()
    # CanCoalesce: DCHECK(merged_offsets.has_value()). Within a block, the
    # offsets of each sequence of a key are within the known range of the
    # key, which only grows ([range-containment]: it is only replaced by
    # its hull with a checked range, when that hull exists, and sequences
    # are recorded after it is computed; loop headers set it before any
    # trap). This holds whatever the facts. So both sequences are within
    # one valid range, and their hull exists.
    k, a, b = Opt.sym('k'), Opt.sym('a'), Opt.sym('b')
    within = lambda r: And(contains(k, r.lo), contains(k, r.hi))
    prove('W9 CanCoalesce: two sequences of a key have a hull',
          [k.present, a.present, b.present, valid_range(k.lo, k.hi),
           valid_range(a.lo, a.hi), valid_range(b.lo, b.hi),
           within(a), within(b)],
          Not(hull(a, b).present))


# The length keys passed to MinLength. Each one is LengthKey(r.length),
# the canonical value (after load elimination replacements) of a length
# returned by TryExtractArrayLength or TryResolveMergeBound (INVENTORY
# counts the calls to MinLength and LengthKey, to check that no other
# kind of value is passed). That length is:
# - in TryExtractArrayLength's constant case, the original value, which
#   decomposes to a constant {o}, below 2^30 (checked there): its key is
#   the constant {o}, or not a constant ({c1 + c2});
# - in its known-length case, or for an alias (TryResolveMergeBound), an
#   ArrayLength operation, kept even when load elimination replaced it,
#   or a recorded allocation length (not a constant). The replacement of
#   an ArrayLength can be any value, including any constant, at least in
#   unreachable code (after an allocation that always traps).
# A constant key {k} must be at least what MinLength returns for it. With
# a DCHECK that constants are below 2^30, the query proves it (and finds
# a counterexample if a constant key can be 2^30 or more). With a test,
# the query refutes it, which shows that the test is needed.
MIN_LENGTH_DCHECK = 'DCHECK_LT(*constant, kMaxArrayLength); return *constant;'
MIN_LENGTH_TEST = ('constant.has_value() && *constant < kMaxArrayLength) { '
                   'return *constant;')


def min_length_form():
    # 'dcheck' or 'test', for the check of constant keys in MinLength.
    text = ''.join(open(os.path.join(V8, f'{SRC}.cc')).read().split())
    has_dcheck = ''.join(MIN_LENGTH_DCHECK.split()) in text
    has_test = ''.join(MIN_LENGTH_TEST.split()) in text
    if has_dcheck == has_test: return None
    return 'dcheck' if has_dcheck else 'test'


def length_key_model():
    # (assumptions, key is a constant, key) for a length key passed to
    # MinLength (see the comment above MIN_LENGTH_DCHECK).
    constant_case = fresh_bool('constant_case')
    o = fresh('o')  # Constant decomposition (constant case).
    key_is_o = fresh_bool('key_is_o')  # The value is {o} itself.
    replaced = fresh_bool('replaced')  # ArrayLength replaced (other cases).
    replacement_is_constant = fresh_bool('replacement_is_constant')
    r = fresh('r')  # The replacement's value, if a constant.
    key_is_constant = If(constant_case, key_is_o,
                         And(replaced, replacement_is_constant))
    key = If(constant_case, o, r)
    return ([Implies(constant_case, ULT(o, bv(K_MAX_ARRAY_LENGTH)))],
            key_is_constant, key)


def min_length_model():
    # (assumptions, value) for what MinLength returns: a constant key itself
    # (if below 2^30 with the test; with the DCHECK, in release builds,
    # any constant key), or the value in the table, recorded by
    # RecordMinLength (at most kMaxInt) or RecordKnownLength (0).
    assumptions, key_is_constant, key = length_key_model()
    table = fresh('table')
    assumptions.append(ULE(table, bv(K_MAX_INT)))
    form = min_length_form()
    returns_key = (key_is_constant if form == 'dcheck' else
                   And(key_is_constant, ULT(key, bv(K_MAX_ARRAY_LENGTH))))
    return assumptions, If(returns_key, key, table)


def check_min_length_keys():
    if min_length_form() is None:
        print('MinLength changed: update check_min_length_keys')
        results.append(False)
        return
    has_dcheck = min_length_form() == 'dcheck'
    assumptions, key_is_constant, key = length_key_model()
    assumptions.append(key_is_constant)
    conclusion = ULT(key, bv(K_MAX_ARRAY_LENGTH))
    if has_dcheck:
        prove('W8 MinLength: constant length keys are below 2^30',
              assumptions, Not(conclusion))
    else:
        refute('W8 MinLength: constant length keys may be 2^30 or more '
               '(the test is needed)', assumptions, conclusion)


# What the well-formedness queries above cover, as counted when they
# were written: OffsetRange constructions, DCHECKs, and the calls to
# MinLength and LengthKey (see check_min_length_keys). When a count
# changes, check that the queries cover the new uses (and update it).
# 60f7a3c58ab added two DCHECKs on the representation of the values
# DecomposeIndex reads (structural, no query needed). bce-series-v2
# removed two DCHECKs on base values, and added one on the representation
# of a trap's index and one in the cast case of CanonicalValue
# (structural), and one in CanCoalesce (W9). The .h counts of calls are
# declarations.
INVENTORY_PATTERNS = {
    'OffsetRange': r'OffsetRange[ (]',
    'DCHECK': r'DCHECK',
    'MinLength calls': r'(?<![A-Za-z:])MinLength\(',
    'LengthKey calls': r'(?<![A-Za-z:])LengthKey\(',
}
INVENTORY = {
    'h': {'OffsetRange': 7, 'DCHECK': 11, 'MinLength calls': 1,
          'LengthKey calls': 1},
    'cc': {'OffsetRange': 11, 'DCHECK': 17, 'MinLength calls': 6,
           'LengthKey calls': 8},
}


def check_inventory():
    ok = True
    for ext, expected in INVENTORY.items():
        text = open(os.path.join(V8, f'{SRC}.{ext}')).read()
        code = '\n'.join(line for line in text.split('\n')
                         if not line.strip().startswith('//'))
        for name, count in expected.items():
            found = len(re.findall(INVENTORY_PATTERNS[name], code))
            if found != count:
                print(f'INVENTORY .{ext}: {found} {name} (expected {count}): '
                      'review the well-formedness queries, then update '
                      'INVENTORY')
                ok = False
    return ok


def refute(name, assumptions, conclusion):
    # The conclusion does NOT follow from the assumptions: there is a
    # counterexample. Documents why the code excludes a case.
    if skipped(name): return
    start = time.time()
    s = SolverFor('QF_BV')
    s.add(*assumptions, Not(conclusion))
    r = s.check()
    results.append(r == sat)
    status = 'ok' if r == sat else f'FAILS ({r})'
    print(f'{status:8} {name} (refuted, {time.time() - start:.1f} s)',
          flush=True)


def check_narrowing():
    # Normalize: an unsigned 64-bit comparison {X < zext(y)} (or {<=})
    # shows that {X} is below 2^32, so it is the comparison of {trunc(X)}
    # with {y} ([narrowed-comparison]).
    X, y = fresh('X', 64), fresh('y')
    low = lambda v: Extract(31, 0, v)
    prove('Narrowing: X <u zext(y)', [ULT(X, ZeroExt(32, y))],
          Not(ULT(low(X), y)))
    prove('Narrowing: X <=u zext(y)', [ULE(X, ZeroExt(32, y))],
          Not(ULE(low(X), y)))
    # The excluded cases: the negated comparison {zext(y) <= X}, signed
    # comparisons, and sign-extended bounds.
    refute('Narrowing excluded: zext(y) <=u X', [ULE(ZeroExt(32, y), X)],
           ULE(y, low(X)))
    refute('Narrowing excluded: X <s zext(y)', [X < ZeroExt(32, y)],
           ULT(low(X), y))
    refute('Narrowing excluded: X <u sext(y)', [ULT(X, SignExt(32, y))],
           ULT(low(X), y))
    # DecomposeIndex reads a 64-bit value as its truncation:
    # {trunc(zext(x)) = trunc(sext(x)) = x}, and {trunc(Y +/- c)} is
    # {trunc(Y) +/- trunc(c)}.
    x, Y, c = fresh('x'), fresh('Y', 64), fresh('c', 64)
    prove('Reading: trunc(zext(x))', [], low(ZeroExt(32, x)) != x)
    prove('Reading: trunc(sext(x))', [], low(SignExt(32, x)) != x)
    prove('Reading: trunc(Y - c)', [], low(Y - c) != low(Y) - low(c))


def main():
    if not check_anchors():
        print('The source changed: update the transcriptions.')
        sys.exit(1)
    if not check_inventory():
        sys.exit(1)
    check_well_formedness()
    check_ranges()
    check_process_comparison()
    check_process_not_equal()
    check_non_negative_index()
    check_guards()
    check_fallback_sequences()
    check_small_bound()
    check_not_equal_induction()
    check_loop_bound()
    check_merge_bound()
    check_non_strict()
    check_not_equal_to_constant()
    check_decreasing_induction()
    check_truncated_addition()
    check_narrowing()
    failed = results.count(False)
    print(f'{len(results) - failed}/{len(results)} queries proved')
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
