# Usage: check-model-anchors.py <v8 dir> [-v]
# Checks that what the Rocq model and the README cite from the C++ code
# is still in src/compiler/turboshaft/wasm-bounds-check-elimination-
# reducer.{h,cc} (the commit named at the top of the README):
# - the C++ identifiers they cite, in [...] in the comments of the .v
#   files and in `...` in the README: CamelCase names (CanonicalValue),
#   members (known_bounds_checks_), and qualified names, other than the
#   names the .v files define;
# - the names of the Z3 lemmas they cite ([induction-constant], in the
#   comments of the .v files and in the README), which must be defined in
#   the comments of the header;
# - the comments of the C++ code they quote ("..." of four words or more,
#   with [...] for elided parts), ignoring comment markers and
#   whitespace.
# Single-word names (Shift, Constant) are not told apart from English, and
# are not checked. With -v, prints the names and lemmas checked. Exits
# with a non-zero status if something is missing.
import glob, os, re, sys

if len(sys.argv) not in (2, 3):
    sys.exit('usage: check-model-anchors.py <v8 dir> [-v]')
SRC = 'src/compiler/turboshaft/wasm-bounds-check-elimination-reducer'
HERE = os.path.dirname(os.path.abspath(__file__))
# Quotes of other sources.
NOT_CPP_QUOTES = ['Formal verification of an SSA-based middle-end for CompCert']

source = ''.join(open(os.path.join(sys.argv[1], f'{SRC}.{ext}')).read()
                 for ext in ['h', 'cc'])
# The text of the comments, without markers, with whitespace collapsed.
comments = ' '.join(m.group(1) for m in re.finditer(r'//+ ?(.*)', source))
comments = ' '.join(comments.split())
lemmas = set(re.findall(r'\[([a-z0-9]+(?:-[a-z0-9]+)+)\]', comments))


def collapse(text):
    return ' '.join(text.split())


files = {}
for path in sorted(glob.glob(os.path.join(HERE, '*.v'))):
    files[os.path.basename(path)] = open(path).read()
readme = open(os.path.join(HERE, 'README.md')).read()

# Names defined in the .v files (and their arguments' names in Variable
# and Hypothesis declarations), which are not C++ names.
coq_names = set()
for text in files.values():
    for m in re.finditer(
            r'\b(?:Definition|Fixpoint|Inductive|Record|Lemma|Theorem|'
            r'Corollary|Variables?|Hypothesis|Scheme|Notation)\s+([\w\s]+?)'
            r'\s*[:(]', text):
        coq_names.update(m.group(1).split())
    for m in re.finditer(r'\|\s*(\w+)\s*:', text):  # constructors
        coq_names.add(m.group(1))

CPP_NAME = re.compile(
    r'\b(?:[A-Z][a-z0-9]+[A-Z]\w*|[a-z][a-z0-9]*(?:_[a-z0-9]+)*_)(?![\w(])')


def citations(name, text, pattern):
    # (line, cited text) for each match of {pattern} in {text}.
    for m in re.finditer(pattern, text, flags=re.S):
        yield text.count('\n', 0, m.start()) + 1, m.group(1)


cited = []  # (file, line, text in brackets or backquotes)
for name, text in files.items():
    for m in re.finditer(r'\(\*.*?\*\)', text, flags=re.S):
        base = text.count('\n', 0, m.start())
        for line, c in citations(name, m.group(0), r'\[([^\[\]]+)\]'):
            cited.append((name, base + line, c))
readme_text = re.sub(r'```.*?```', lambda m: '\n' * m.group(0).count('\n'),
                     readme, flags=re.S)
for line, c in citations('README.md', readme_text, r'`([^`]+)`'):
    # Branches and planted bugs are in kebab case too, but are not lemmas.
    if not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)+', c):
        cited.append(('README.md', line, c))
for line, c in citations('README.md', re.sub(r'`[^`]*`', '', readme_text),
                         r'\[([a-z0-9]+(?:-[a-z0-9]+)+)\]'):
    cited.append(('README.md', line, c))

missing = []
names_checked, lemmas_checked = set(), set()
for f, line, c in cited:
    if re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)+', c):
        lemmas_checked.add(c)
        if c not in lemmas:
            missing.append(f'{f}:{line}: Z3 lemma [{c}]')
        continue
    for part in re.split(r'::|\.|->', c):
        for n in CPP_NAME.findall(part):
            if n in coq_names: continue
            names_checked.add(n)
            if n not in source:
                missing.append(f'{f}:{line}: {n}')

# Quotes of C++ comments.
quotes_checked = 0
for name, text in [*files.items(), ('README.md', readme_text)]:
    flat = collapse(text)
    for m in re.finditer(r'"([^"]+)"', flat):
        quote = m.group(1)
        if len(quote.split()) < 4 or quote in NOT_CPP_QUOTES: continue
        quotes_checked += 1
        for part in quote.split('[...]'):
            part = part.strip(' .')
            if part and part not in comments:
                missing.append(f'{name}: quote "{part[:60]}..."')

if '-v' in sys.argv:
    print(' '.join(sorted(names_checked)))
    print(' '.join(sorted(lemmas_checked)))
print(f'{len(names_checked)} C++ names, {len(lemmas_checked)} Z3 lemmas, '
      f'{quotes_checked} quotes checked')
for m in missing:
    print('MISSING', m)
sys.exit(1 if missing else 0)
