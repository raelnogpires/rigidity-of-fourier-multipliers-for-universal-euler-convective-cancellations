#!/usr/bin/env python3
"""Reject admitted Lean proofs in active sources; compilation remains essential.

This lexical check handles nested block comments, line comments, and strings.
It cannot establish that a theorem's type expresses its intended mathematics.
"""
from pathlib import Path
import re


def code_only(text):
    output = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                output.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1; break
                else:
                    output.append('\n' if text[i] == '\n' else ' '); i += 1
        else:
            output.append(text[i]); i += 1
    assert depth == 0, 'Unclosed block comment'
    return ''.join(output)


def main():
    root = Path(__file__).resolve().parents[1]
    paths = sorted((root / 'lean').rglob('*.lean'))
    assert paths
    for path in paths:
        code = code_only(path.read_text())
        forbidden = re.search(r'\b(sorry|admit|axiom|unsafe)\b', code)
        assert forbidden is None, f'{path.relative_to(root)}: {forbidden.group()}'
    print(f'PASS source hygiene: {len(paths)} Lean files; no admitted proofs or user axioms')
    print('This is not a substitute for compilation, axiom inspection or semantic review.')


if __name__ == '__main__':
    main()
