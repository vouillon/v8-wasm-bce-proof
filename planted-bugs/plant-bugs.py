# Plants bugs in the Wasm BCE analysis, one at a time, and measures how
# long the random loop test takes to find each one (and whether
# test/mjsunit/wasm/bounds-check-elimination.js finds it). Each bug is a
# one-line edit of the source, which is restored at the end; d8 is
# rebuilt for each one, in $V8_BUILD_DIR (default: out/x64.optdebug of
# $V8_DIR, the V8 checkout, which is required). Results go to
# $FUZZ_DIR/mutants.json (after each bug), logs to $FUZZ_DIR/mutant-logs
# (default: ./plant-bugs-results). At the end, once the original source
# is rebuilt, each seed that found a bug is run again on it: a seed that
# also fails there ("baseline": "fails") did not find the bug, and the
# control entry "(original)" says whether the original passes
# bounds-check-elimination.js.
# Usage: plant-bugs.py [--set loops|persistence|truncation|narrowing|guards|
#                             emission|dchecks]
#                      [names...]
# Without --set, named bugs are looked up in all the sets, and with no
# names, the loops set runs.
# The "loops" set (the default) targets the loop reasoning, the
# "persistence" set what makes facts hold at other program points:
# canonical values, merges of snapshots, and conditions, and the
# "truncation" set the decomposition of truncated 64-bit additions
# (bce-loop-ideas branch), the "narrowing" set the narrowing of 64-bit
# comparisons and the reading of 64-bit values as their truncations
# (bce-loop-ideas, 7c94e0ee3b6). The "guards" set targets the guards of
# fallback sequences, and the "emission" set how the reducer emits them,
# which is not checked with Z3. The "dchecks" set replaces checks that seem
# redundant by DCHECKs: one that is "found" is not redundant (the DCHECK
# fails, in unreachable code with contradictory facts for instance).
import ctypes, json, multiprocessing, os, random, signal, subprocess, sys, time

# Kills a child process (d8) when its parent (a worker) dies: terminating
# the pool of workers does not kill their children otherwise, and a d8
# running a test that does not terminate would then run forever.
_libc = ctypes.CDLL(None, use_errno=True)
PR_SET_PDEATHSIG = 1


def die_with_parent():
    _libc.prctl(PR_SET_PDEATHSIG, signal.SIGKILL)


# The V8 checkout (or worktree) and its build directory.
if 'V8_DIR' not in os.environ:
    sys.exit('V8_DIR must be the V8 checkout (see the comment at the top)')
V8 = os.environ['V8_DIR']
OUT = os.environ.get('V8_BUILD_DIR', os.path.join(V8, 'out/x64.optdebug'))
# The edited files: the .cc file, unless a bug names another one.
SRC = 'src/compiler/turboshaft/wasm-bounds-check-elimination-reducer.cc'
HEADER = 'src/compiler/turboshaft/wasm-bounds-check-elimination-reducer.h'
HERE = os.environ.get('FUZZ_DIR', 'plant-bugs-results')
LOGS = os.path.join(HERE, 'mutant-logs')
BUDGET = int(os.environ.get('BUDGET', 240))  # seconds of fuzzing per mutant
WORKERS = 8

MUTANTS = [
    # EntryLowerBound: {k <= x} taken as {k < x}.
    ('entry-strict', '(relation->is_strict() ? 1 : 0)', '1'),
    # EntryLowerBound: {x} excluded from 0 by a branch, whichever way.
    ('excluded-no-holds', 'if (holds && CanonicalValue(condition) == x)',
     'if (CanonicalValue(condition) == x)'),
    # TryResolveMergeBound: off by one when ruling out phi constants.
    ('merge-off-by-one', 'if (candidate < bound.x_lower_bound) continue;',
     'if (candidate <= bound.x_lower_bound) continue;'),
    # TryMatchInductionVariable: no limit on the step.
    ('step-limit', '|| step.offset > kMaxArrayLength) {', ') {'),
    # TryMatchInductionVariable: negative initial values.
    ('negative-init', '|| static_cast<int32_t>(*init) < 0) {', ') {'),
    # IsSmallBound: unsigned comparison with {a.length - r}.
    ('small-bound-unsigned',
     'return length.has_value() && (is_signed || length->reduction == 0);',
     'return length.has_value();'),
    # IsSmallBound: inclusive constant bound treated as strict.
    ('const-limit', '(inclusive ? 0 : 1)', '1'),
    # FindNotEqualBound: only {i != x} needed after unrolling.
    ('unrolled-tests', 'if (candidate.offsets != all_offsets) continue;',
     'if ((candidate.offsets & 1) == 0 && all_offsets != 0) continue;'),
    # FindNotEqualBound: {x} not required to be loop-invariant. Possibly
    # not observable: EntryLowerBound only finds a lower bound for a
    # constant, or from conditions dominating the loop entry, which cannot
    # refer to a value computed in the loop (unless it has the same
    # canonical value as one computed before it, which is then invariant).
    ('invariant-x',
     '!Dominates(&graph_.Get(graph_.BlockOf(candidate.x_value)), forward)) {',
     'false) {'),
    # RecordLoopBound: offsets 0 to r instead of 0 to r - 1.
    ('loop-bound-off-by-one',
     'uint32_t last = length->reduction - 1;\n'
     '  TRACE("  Loop induction: offsets [0, " << last << "] of " << induction.value',
     'uint32_t last = length->reduction;\n'
     '  TRACE("  Loop induction: offsets [0, " << last << "] of " << induction.value'),
    # ProcessNotEqual: {x + m} not required to be within bounds.
    ('not-equal-length',
     'if (!known.has_value() || !known->Contains(last) ||',
     'if (!known.has_value() ||'),
    # Control: !(a <s b) taken as (b <s a).
    ('normalize-signed',
     'case Kind::kSignedLessThan:\n'
     '        relation = Relation{Kind::kSignedLessThanOrEqual,',
     'case Kind::kSignedLessThan:\n'
     '        relation = Relation{Kind::kSignedLessThan,'),
]

# Bugs in what makes facts hold at other program points.
STRUCTURAL_PHI = '''    case Opcode::kPhi: {
      const PhiOp& phi = op.Cast<PhiOp>();
      if (phi.input_count != 2) break;
      key = StructuralKey{op.opcode, 0, 0, CanonicalValue(phi.input(0), depth + 1),
                          CanonicalValue(phi.input(1), depth + 1)};
      break;
    }
'''
STRUCTURAL_STRUCT_GET = '''    case Opcode::kStructGet: {
      const StructGetOp& get = op.Cast<StructGetOp>();
      key = StructuralKey{op.opcode, static_cast<uint64_t>(get.field_index), 0,
                          CanonicalValue(get.object(), depth + 1),
                          OpIndex::Invalid()};
      break;
    }
'''
STRUCTURAL_ARRAY_GET = '''    case Opcode::kArrayGet: {
      const ArrayGetOp& get = op.Cast<ArrayGetOp>();
      key = StructuralKey{op.opcode, 0, 0, CanonicalValue(get.array(), depth + 1),
                          CanonicalValue(get.index(), depth + 1)};
      break;
    }
'''
BITCAST = '    case Opcode::kTaggedBitcast: {'
PERSISTENCE_MUTANTS = [
    # CanonicalValue: the kind of the operation is ignored.
    ('binop-kind', 'static_cast<uint64_t>(binop.kind) |', '0 |'),
    ('shift-kind', 'static_cast<uint64_t>(shift.kind) |', '0 |'),
    # (In ChangeOptions since 0f9ceaf5935.)
    ('change-kind', 'return static_cast<uint64_t>(kind) |', 'return 0 |'),
    # CanonicalValue: {a - b} is {b - a}.
    ('commutative-all',
     'if (WordBinopOp::IsCommutative(binop.kind) && right < left) {',
     'if (right < left) {'),
    # CanonicalValue: the bitcast of any reference (only observable with
    # a moving GC).
    ('bitcast-smi', '!IsKnownSmi(bitcast.input())) {', 'false) {'),
    # CanonicalValue: phis, loads of struct fields and of array elements
    # with the same inputs are the same value.
    ('phi-structural', BITCAST, STRUCTURAL_PHI + BITCAST),
    ('struct-get-structural', BITCAST, STRUCTURAL_STRUCT_GET + BITCAST),
    ('array-get-structural', BITCAST, STRUCTURAL_ARRAY_GET + BITCAST),
    # BeginBlock: a merge keeps the facts of its first predecessor.
    ('merge-first-pred-bounds',
     'known_bounds_checks_.StartNewSnapshot(\n      base::VectorOf(predecessor_bounds_check_snapshots_));',
     'known_bounds_checks_.StartNewSnapshot(\n      predecessor_bounds_check_snapshots_.front());'),
    ('merge-first-pred-non-negative',
     'known_non_negative_offsets_.StartNewSnapshot(\n      base::VectorOf(predecessor_non_negative_snapshots_));',
     'known_non_negative_offsets_.StartNewSnapshot(\n      predecessor_non_negative_snapshots_.front());'),
    ('merge-first-pred-min-length',
     'known_min_lengths_.StartNewSnapshot(\n      base::VectorOf(predecessor_min_length_snapshots_));',
     'known_min_lengths_.StartNewSnapshot(\n      predecessor_min_length_snapshots_.front());'),
    # BeginBlock: length aliases flow into merges where some predecessor
    # has none.
    ('alias-leak', 'if (all_predecessors_have_length_aliases) {',
     'if (all_predecessors_have_length_aliases ||\n'
     '        !predecessor_length_alias_snapshots_.empty()) {'),
    # ForEachCondition: {a & b} not holding shows that neither holds (the
    # rule for {a & b} holding applies to any operands in bce-series).
    ('and-not-holds', 'binop->kind == WordBinopOp::Kind::kBitwiseAnd && holds) {',
     'binop->kind == WordBinopOp::Kind::kBitwiseAnd) {'),
    # ForEachCondition: {a | b} holding shows that both hold.
    ('or-holds', 'binop->kind == WordBinopOp::Kind::kBitwiseOr && !holds',
     'binop->kind == WordBinopOp::Kind::kBitwiseOr'),
    # ForEachCondition: {a == c} is {!a} for any constant {c}.
    ('eqz-any', '*constant == 0) {', 'true) {'),
]

# Bugs in the decomposition of {trunc(x + c)} (DecomposeIndex,
# ExistingTruncation).
TRUNCATION_MUTANTS = [
    # (truncation-same-block and truncation-dominance targeted the
    # dominance filter of ExistingTruncation, which bce-series-v2 removed:
    # guards no longer use truncations, see GUARD_MUTANTS.)
    # {trunc(x - c)} is {trunc(x) + c}. (Edits for bce-series, where the
    # truncated addition no longer accepts a constant on the left.)
    ('truncation-sub-sign',
     'offset += op->kind == WordBinopOp::Kind::kAdd ? *constant : -*constant;\n'
     '      index = base;',
     'offset += *constant;\n      index = base;'),
    # Any operation with a constant on the right is an addition or a
    # subtraction.
    ('truncation-any-op',
     ' ||\n'
     '          (op->kind != WordBinopOp::Kind::kAdd &&\n'
     '           op->kind != WordBinopOp::Kind::kSub)) {\n'
     '        break;',
     ') {\n        break;'),
]

# Bugs in the narrowing of 64-bit comparisons {X < zext(y)} (Normalize)
# and in the reading of 64-bit values as their truncations
# (DecomposeIndex, TruncationKey).
NARROWING_MUTANTS = [
    # Signed comparisons are narrowed too.
    ('narrow-signed',
     'if (relation.kind != Kind::kUnsignedLessThan &&\n'
     '      relation.kind != Kind::kUnsignedLessThanOrEqual) {',
     'if (relation.kind == Kind::kEqual) {'),
    # Any extension on the right side, including a sign extension.
    ('narrow-any-change', '.TryCast<Opmask::kChangeUint32ToUint64>();',
     '.TryCast<ChangeOp>();'),
    # A narrowed comparison eliminates a trap.
    ('narrowed-trap-eliminated', 'reduction == 0 && !relation->narrowed;',
     'reduction == 0;'),
    # The value standing for {trunc(X)} is used as a truncation (and so
    # as an index, possibly by a guard).
    ('truncation-placeholder',
     '  OpIndex canonical = CanonicalValue(x);\n  return values_by_structure_',
     '  OpIndex canonical = CanonicalValue(x);\n'
     '  truncations_.emplace(canonical, canonical);\n'
     '  return values_by_structure_'),
    # The {wide} flag is not passed for the left side of a narrowed
    # relation (60f7a3c58ab): the 64-bit value is then read as a 32-bit
    # base (found by the DCHECKs of DecomposeIndex in debug builds).
    ('wide-dropped-bounds-check',
     'ExtractBaseAndOffset(relation.left, relation.narrowed);\n'
     '  OpIndex base = decomposed.base;',
     'ExtractBaseAndOffset(relation.left, false);\n'
     '  OpIndex base = decomposed.base;'),
    ('wide-dropped-small-bound',
     'BaseAndOffset left = ExtractBaseAndOffset(relation.left, relation.narrowed);',
     'BaseAndOffset left = ExtractBaseAndOffset(relation.left, false);'),
    ('wide-dropped-non-negative',
     'BaseAndOffset result = ExtractBaseAndOffset(index, relation.narrowed);',
     'BaseAndOffset result = ExtractBaseAndOffset(index, false);'),
    # {trunc(Y - c)} is {trunc(Y) + c}.
    ('wide-sub-sign',
     'binop->kind == WordBinopOp::Kind::kAdd ? *constant : -*constant;',
     '*constant;'),
]

# Bugs in the guards of fallback sequences (bce-series-v3: built from the
# index and the length of the sequence's first trap, see GuardIndex).
GUARD_MUTANTS = [
    # The guard ignores the offset of the index it is built from.
    ('guard-index-delta', 'uint32_t delta = offset - seq.index_offset();',
     'uint32_t delta = offset;', HEADER),
    ('guard-delta-sign', 'uint32_t delta = offset - seq.index_offset();',
     'uint32_t delta = seq.index_offset() - offset;', HEADER),
    # When coalescing moves the guard earlier, it keeps the offset of the
    # later index.
    ('coalesce-keeps-offset',
     '      index_ = other.index_;\n      index_offset_ = other.index_offset_;\n',
     '      index_ = other.index_;\n', HEADER),
    # ... or the later index itself, computed after the guard.
    ('coalesce-keeps-index',
     '      index_ = other.index_;\n      index_offset_ = other.index_offset_;\n',
     '', HEADER),
    # ... or the length of the later trap, which may be computed after the
    # guard.
    ('coalesce-keeps-length',
     '      array_length_ = other.array_length_;\n', '', HEADER),
    # ... or the facts known at the later start. This breaks the invariant
    # checked by check-z3-decisions.py ("Coalesce: invariant"), but seems
    # unobservable: the guard computed is the same (see the README).
    ('coalesce-keeps-known',
     '      known_offsets_ = other.known_offsets_;\n', '', HEADER),
    ('coalesce-keeps-non-negative',
     '      non_negative_offsets_ = other.non_negative_offsets_;\n', '',
     HEADER),
]

# Bugs in the emission of fallback sequences by the reducer (bce-series-v3),
# which the Z3 queries do not model.
EMISSION_MUTANTS = [
    # A sequence is also emitted within the fallback code of another one,
    # which removes its covered traps from the rest of the graph, including
    # the fast path of the other sequence (see in_fallback_code_).
    ('emit-in-fallback-code', '    if (in_fallback_code_) return;\n', '',
     HEADER),
    ('fallback-mode-not-set',
     '    ScopedModification<bool> set_true(&in_fallback_code_, true);\n', '',
     HEADER),
    # The fallback code lacks the last covered trap: when the guard fails
    # on its offset, the fallback code reaches its Unreachable.
    ('fallback-drops-last-trap',
     '    __ CloneAndInlineTrappingInstructions(seq.start_index(), '
     'seq.end_index(),',
     '    __ CloneAndInlineTrappingInstructions(seq.start_index(), '
     '__ input_graph().PreviousIndex(seq.end_index()),', HEADER),
    # The guard accepts an index equal to the length.
    ('guard-le',
     '    GOTO_IF_NOT(LIKELY(__ Uint32LessThan(index, length)), fallback_code);',
     '    GOTO_IF_NOT(LIKELY(__ Uint32LessThanOrEqual(index, length)), '
     'fallback_code);', HEADER),
    ('two-sided-guard-le',
     '    GOTO_IF_NOT(LIKELY(__ Uint64LessThan(end, '
     '__ ChangeUint32ToUint64(length))),',
     '    GOTO_IF_NOT(LIKELY(__ Uint64LessThanOrEqual(end, '
     '__ ChangeUint32ToUint64(length))),', HEADER),
]

# Checks that seem redundant, turned into DCHECKs.
DCHECK_MUTANTS = [
    ('hull-size', 'if (static_cast<int32_t>(size) < 0) continue;',
     'DCHECK_GE(static_cast<int32_t>(size), 0);', HEADER),
    ('extend-down-upper',
     '      !OffsetRange::IsValidRange(non_negative->lower(), range.lower()) ||\n'
     '      !OffsetRange::IsValidRange(non_negative->lower(), range.upper())) {\n'
     '    return std::nullopt;\n'
     '  }\n',
     '      !OffsetRange::IsValidRange(non_negative->lower(), range.lower())) {\n'
     '    return std::nullopt;\n'
     '  }\n'
     '  DCHECK(OffsetRange::IsValidRange(non_negative->lower(), range.upper()));\n'),
    ('invariant-x-dcheck',
     '    if (!TryExtractI32Const(candidate.x_value).has_value() &&\n'
     '        !Dominates(&graph_.Get(graph_.BlockOf(candidate.x_value)), forward)) {\n'
     '      continue;\n'
     '    }',
     '    DCHECK(TryExtractI32Const(candidate.x_value).has_value() ||\n'
     '           Dominates(&graph_.Get(graph_.BlockOf(candidate.x_value)), forward));'),
]

BCE = ['--turboshaft-wasm-bounds-check-elimination',
       '--turboshaft-verify-wasm-bounds-check-elimination']
LOOP = BCE + ['--allow-natives-syntax', '--liftoff', '--no-wasm-lazy-compilation',
              '--wasm-tiering-budget=1000000000']
OLD = BCE + ['--no-liftoff', '--no-wasm-lazy-compilation']
OPTIONAL = ['--no-wasm-loop-unrolling', '--no-wasm-loop-peeling',
            '--no-turboshaft-wasm-load-elimination']


def d8(flags, test, args=(), timeout=300):
    cmd = [os.path.join(OUT, 'd8'), *flags, 'test/mjsunit/mjsunit.js', test,
           *(['--', *args] if args else [])]
    try:
        r = subprocess.run(cmd, cwd=V8, capture_output=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, preexec_fn=die_with_parent)
        return r.returncode, (r.stdout + r.stderr).decode(errors='replace'), cmd
    except subprocess.TimeoutExpired:
        return 'timeout', '', cmd


def kind(log):
    if 'wrongly eliminated' in log or 'Fatal' in log or 'Check failed' in log:
        return 'abort'
    if 'MjsUnitAssertionError' in log or 'Failure' in log:
        return 'mismatch'
    return 'other'


LOOP_TEST = 'test/mjsunit/wasm/bounds-check-elimination-loops.js'
OLD_TEST = 'test/mjsunit/wasm/bounds-check-elimination.js'

# The runs of all the workers, including those terminated when another
# one finds the bug.
RUNS = None


def init_worker(runs):
    global RUNS
    RUNS = runs
    # Workers are terminated with SIGTERM (Pool.terminate).
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


def old_test():
    code, log, _ = d8(OLD, OLD_TEST, timeout=900)
    return log, ('pass' if code == 0 else 'timeout' if code == 'timeout'
                 else kind(log))


def fuzz_one(deadline):
    random.seed(os.urandom(8))
    runs = timeouts = 0
    while time.time() < deadline:
        seed = random.randrange(1, 2**31)
        flags = LOOP + [f for f in OPTIONAL if random.random() < 0.3]
        code, log, cmd = d8(flags, LOOP_TEST, [str(seed), '200'], timeout=120)
        runs += 1
        with RUNS.get_lock(): RUNS.value += 1
        # A timeout is not a detection: the random test itself may loop
        # (which is a bug of the test, to report).
        if code == 'timeout':
            timeouts += 1
            print(f'TIMEOUT seed {seed} flags {" ".join(flags)}', flush=True)
            continue
        if code != 0:
            return {'seed': seed, 'flags': flags, 'code': code, 'kind': kind(log),
                    'log': log[-4000:], 'time': time.time(), 'runs': runs,
                    'timeouts': timeouts}
    return {'runs': runs, 'timeouts': timeouts}


def save(results):
    os.makedirs(HERE, exist_ok=True)
    with open(os.path.join(HERE, 'mutants.json'), 'w') as f:
        json.dump(results, f, indent=1)


def build():
    b = subprocess.run(['autoninja', '-C', OUT, 'd8'], cwd=V8,
                       capture_output=True)
    return b.returncode == 0, (b.stdout + b.stderr).decode(errors='replace')


def baseline(results):
    # Runs each seed that found a bug on the original build: a seed that
    # also fails there did not find the bug.
    for entry in results:
        if 'seed' not in entry: continue
        code, _, _ = d8(entry['flags'], LOOP_TEST, [str(entry['seed']), '200'],
                        timeout=120)
        entry['baseline'] = ('pass' if code == 0 else 'timeout'
                             if code == 'timeout' else 'fails')
        if entry['baseline'] != 'pass':
            print(f'{entry["name"]}: seed {entry["seed"]} also fails on the '
                  f'original ({entry["baseline"]})', flush=True)


def main():
    # A SIGTERM (kill, timeout) runs the finally clause below, which
    # restores the source, as an interrupt does.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit('terminated'))
    args = sys.argv[1:]
    sets = {'loops': MUTANTS, 'persistence': PERSISTENCE_MUTANTS,
            'truncation': TRUNCATION_MUTANTS, 'narrowing': NARROWING_MUTANTS,
            'guards': GUARD_MUTANTS, 'emission': EMISSION_MUTANTS,
            'dchecks': DCHECK_MUTANTS}
    if args[:1] == ['--set']:
        mutants = sets[args[1]]
        args = args[2:]
    elif args:
        # Bugs named without a set are looked up in all the sets.
        mutants = [m for ms in sets.values() for m in ms]
    else:
        mutants = MUTANTS
    names = args or [m[0] for m in mutants]
    unknown = set(names) - {m[0] for m in mutants}
    if unknown:
        sys.exit(f'unknown bugs: {" ".join(sorted(unknown))}')
    os.makedirs(LOGS, exist_ok=True)
    originals = {path: open(os.path.join(V8, path)).read()
                 for path in [SRC, HEADER]}
    written = {}  # The edited files, with the edit written.

    def restore(path):
        # Unless someone else changed the file meanwhile: their version,
        # which may still contain the planted bug, is then kept, and the
        # run stops (the originals are stale).
        current = open(os.path.join(V8, path)).read()
        written_text = written.pop(path, None)
        if current == written_text:
            open(os.path.join(V8, path), 'w').write(originals[path])
        elif current != originals[path]:
            print(f'{path} was changed by someone else during the run, and '
                  'is not restored: check that it does not contain the '
                  'planted bug, and rebuild d8', flush=True)
            return False
        return True

    results = []
    completed = False
    try:
        for name, old, new, *path in mutants:
            if name not in names: continue
            path = path[0] if path else SRC
            original = originals[path]
            if original.count(old) != 1:
                # The source changed: update the edit.
                print(f'{name}: edit found {original.count(old)} times', flush=True)
                results.append({'name': name, 'edit': 'not found'})
                continue
            if open(os.path.join(V8, path)).read() != original:
                print(f'{path} was changed by someone else during the run: '
                      'stopping', flush=True)
                break
            written[path] = original.replace(old, new)
            open(os.path.join(V8, path), 'w').write(written[path])
            built, build_log = build()
            # d8 keeps the bug until the next build.
            if not restore(path):
                break
            if not built:
                print(f'{name}: build failed', flush=True)
                with open(os.path.join(LOGS, f'{name}-build.log'), 'w') as f:
                    f.write(build_log[-20000:])
                results.append({'name': name, 'build': 'failed'})
                save(results)
                continue
            log, old_result = old_test()
            with open(os.path.join(LOGS, f'{name}-old.log'), 'w') as f: f.write(log[-20000:])
            start = time.time()
            runs_counter = multiprocessing.Value('i', 0)
            with multiprocessing.Pool(WORKERS, init_worker,
                                      (runs_counter,)) as pool:
                pending = [pool.apply_async(fuzz_one, (start + BUDGET,))
                           for _ in range(WORKERS)]
                found, timeouts = None, 0
                while pending and not found:
                    time.sleep(1)
                    for p in [p for p in pending if p.ready()]:
                        pending.remove(p)
                        r = p.get()
                        timeouts += r['timeouts']
                        if 'seed' in r: found = r
                pool.terminate()
            runs = runs_counter.value
            entry = {'name': name, 'old_test': old_result, 'runs': runs}
            if timeouts: entry['timeouts'] = timeouts
            if found:
                entry.update(found=round(found['time'] - start), seed=found['seed'],
                             kind=found['kind'], code=found['code'],
                             flags=found['flags'])
                with open(os.path.join(LOGS, f'{name}-loop.log'), 'w') as f:
                    f.write(' '.join(found['flags']) + f'\nseed {found["seed"]}\n\n' + found['log'])
            results.append(entry)
            save(results)
            print(json.dumps({k: v for k, v in entry.items() if k != 'flags'}), flush=True)
        else:
            completed = True
    finally:
        restored = all([restore(path) for path in list(written)])
        built, _ = build()
        if not built:
            print('the original source does not build', flush=True)
        elif completed and restored:
            # Controls, on the original build.
            _, old_result = old_test()
            results.append({'name': '(original)', 'old_test': old_result})
            if old_result != 'pass':
                print(f'the original fails {OLD_TEST} ({old_result})', flush=True)
            baseline(results)
        save(results)


if __name__ == '__main__':
    main()
