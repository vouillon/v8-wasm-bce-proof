# Usage: check-normalization.py <v8 dir> [<d8>]
#
# Checks that the default pipeline moves constants to the right of
# additions before bounds check elimination, which only reads {x + c}:
# after {a[i]}, the check of {a[1 + i]} must extend the known offsets of
# {i} to [0, 1], as for {a[i + 1]}. The normalization comes from loop
# peeling (its machine optimizations run on every function), so this
# fails if the pipeline changes. No V8 test can check it: unit tests do
# not run the pipeline, and mjsunit tests only see results.
#
# Needs a debug (or optdebug) d8, for the trace flag (default:
# <v8 dir>/out/x64.optdebug/d8). With --no-wasm-loop-peeling, the check of
# {a[1 + i]} is not recognized (precision only), which is reported for
# information.
import os, re, subprocess, sys, tempfile

if len(sys.argv) < 2:
    sys.exit('usage: check-normalization.py <v8 dir> [<d8>]')
V8 = sys.argv[1]
D8 = sys.argv[2] if len(sys.argv) > 2 else os.path.join(V8, 'out/x64.optdebug/d8')

PROBE = '''
d8.file.execute('test/mjsunit/wasm/wasm-module-builder.js');
let builder = new WasmModuleBuilder();
let array = builder.addArray(kWasmI32);
let sig = makeSig([wasmRefNullType(array), kWasmI32], [kWasmI32]);
// a[i] + a[i + 1], and a[i] + a[1 + i].
for (let [name, left] of [['right', false], ['left', true]]) {
  let plus1 = left ? [...wasmI32Const(1), kExprLocalGet, 1, kExprI32Add]
                   : [kExprLocalGet, 1, ...wasmI32Const(1), kExprI32Add];
  builder.addFunction(name, sig).addBody([
    kExprLocalGet, 0, kExprLocalGet, 1, kGCPrefix, kExprArrayGet, array,
    kExprLocalGet, 0, ...plus1, kGCPrefix, kExprArrayGet, array,
    kExprI32Add]).exportFunc();
}
let instance = builder.instantiate();
for (let name of ['right', 'left']) {
  print('== ' + name);
  %WasmTierUpFunction(instance.exports[name]);
}
'''
FLAGS = ['--turboshaft-wasm-bounds-check-elimination',
         '--turboshaft-trace-wasm-bounds-check-elimination',
         '--allow-natives-syntax', '--liftoff', '--no-wasm-lazy-compilation']


def recognized(extra):
    # For each function, whether the second check extends the known
    # offsets of the base of the first one to [0, 1].
    with tempfile.NamedTemporaryFile('w', suffix='.js') as f:
        f.write(PROBE)
        f.flush()
        out = subprocess.run([D8, *FLAGS, *extra, f.name], cwd=V8,
                             capture_output=True, text=True).stdout
    result = {}
    for name, body in re.findall(r'== (\w+)\n(.*?)(?===|\Z)', out, re.S):
        result[name] = bool(re.search(r'Known offsets for base \d+ and '
                                      r'length \d+: \[0, 1\]', body))
    return result


default = recognized([])
print(f'default flags: {default}')
print(f'--no-wasm-loop-peeling (information): '
      f'{recognized(["--no-wasm-loop-peeling"])}')
if default != {'right': True, 'left': True}:
    sys.exit('FAILS: with the default flags, a[1 + i] is not recognized '
             'like a[i + 1] (constants are no longer normalized before '
             'the analysis, or the trace format changed)')
print('ok')
