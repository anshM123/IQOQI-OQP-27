"""Scan Lean sources for forbidden proof shortcuts, ignoring comments and string literals.

Usage:  python scan_forbidden.py [DIR ...]      (default: OQP27 CGLMPRigidity)

Reports every occurrence, in code, of the tokens `sorry`, `admit`, `native_decide`, `axiom` (as a declaration
keyword), `implemented_by`, `extern`, `unsafe` and `opaque` (an `opaque` constant could hide an unproved value; none is
used here).  Doc strings, `--` comments, nested `/- ... -/` comments and string literals are skipped.  The definitive check
is `#print axioms` (the files `*Axioms.lean`); this scan is a quick syntactic cross-check.  Exit code 1 if anything is found.
"""
import os
import re
import sys

TOKENS = re.compile(r'(?<![\w.\'])(sorry|admit|native_decide|axiom|implemented_by|extern|unsafe|opaque)(?![\w\'])')


def strip_comments_and_strings(src):
    """Replace comments and string literals by spaces (newlines kept, so line numbers stay correct)."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth > 0:
            if src.startswith('/-', i):
                depth += 1; out.append('  '); i += 2
            elif src.startswith('-/', i):
                depth -= 1; out.append('  '); i += 2
            else:
                out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif src.startswith('/-', i):
            depth = 1; out.append('  '); i += 2
        elif src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            seg = src[i:j + 1]
            out.append(''.join('\n' if c == '\n' else ' ' for c in seg)); i = j + 1
        elif src[i] == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == '\\' and i + 3 < n and src[i + 3] == "'")):
            k = i + 3 if src[i + 2] == "'" else i + 4          # character literal such as 'a' or '\n'
            out.append(' ' * (k - i)); i = k
        else:
            out.append(src[i]); i += 1
    return ''.join(out)


def main():
    dirs = sys.argv[1:] or ['OQP27', 'CGLMPRigidity']
    found, nfiles = [], 0
    for d in dirs:
        for root, _, files in os.walk(d):
            for f in sorted(files):
                if not f.endswith('.lean'):
                    continue
                p = os.path.join(root, f)
                nfiles += 1
                code = strip_comments_and_strings(open(p, encoding='utf-8').read())
                for ln, line in enumerate(code.split('\n'), 1):
                    for m in TOKENS.finditer(line):
                        found.append(f'{p}:{ln}: {m.group(1)}')
    print(f'scanned {nfiles} Lean files in {", ".join(dirs)}')
    if found:
        print('\n'.join(found))
        sys.exit(1)
    print('no sorry / admit / native_decide / axiom / implemented_by / extern / unsafe / opaque in code')


if __name__ == '__main__':
    main()
