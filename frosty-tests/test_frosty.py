#!/usr/bin/env python3
"""Black-box regression tests. Python standard library only; requires .NET 8 SDK."""
import itertools
import os
from pathlib import Path
import re
import subprocess
import unittest

REPO = Path(os.environ.get('FROSTY_REPO', Path(__file__).resolve().parent.parent)).resolve()
DOTNET = os.environ.get('DOTNET', 'dotnet')
DLL = REPO / 'bin' / 'Release' / 'net8.0' / 'frosty.dll'


def atom_names(f):
    if isinstance(f, str):
        return {f}
    return set().union(*(atom_names(x) for x in f[1:]))


def render(f):
    if isinstance(f, str):
        return f
    if f[0] == 'not':
        return f'~({render(f[1])})'
    symbol = {'and': '&', 'or': '|', 'imp': '->', 'iff': '<->'}[f[0]]
    return f'({render(f[1])} {symbol} {render(f[2])})'


def evaluate(f, values):
    if isinstance(f, str):
        return values[f]
    a = evaluate(f[1], values)
    if f[0] == 'not':
        return not a
    b = evaluate(f[2], values)
    return {'and': a and b, 'or': a or b, 'imp': not a or b, 'iff': a == b}[f[0]]


def is_valid(premises, conclusion):
    names = sorted(set().union(*(atom_names(f) for f in [*premises, conclusion])))
    for bits in itertools.product([False, True], repeat=len(names)):
        values = dict(zip(names, bits))
        if all(evaluate(p, values) for p in premises) and not evaluate(conclusion, values):
            return False
    return True


class FrostyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (REPO / 'frosty.fsproj').is_file():
            raise RuntimeError(f'Set FROSTY_REPO to the repository root; not found at {REPO}')
        result = subprocess.run([DOTNET, 'build', str(REPO / 'frosty.fsproj'), '-c', 'Release', '--nologo'],
                                capture_output=True, text=True, timeout=180)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)

    def cli(self, *args):
        result = subprocess.run([DOTNET, str(DLL), *args], capture_output=True,
                                text=True, encoding='utf-8', timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(result.stderr.strip(), result.stderr)
        return re.sub(r'\x1b\[[0-9;]*m', '', result.stdout).strip()

    def test_help(self):
        for args in [(), ('help',), ('help', 'prove')]:
            with self.subTest(args=args):
                self.assertIn('prove', self.cli(*args).lower())

    def test_operator_aliases(self):
        groups = [(['¬', '~', '!', '-'], '¬P'),
                  (['∧', '&', '&&'], 'P ∧ Q'),
                  (['∨', '|', '||'], 'P ∨ Q'),
                  (['⇒', '→', '⊃', '->', '-->'], 'P ⇒ Q'),
                  (['⇔', '⟷', '≡', '<->', '<-->'], 'P <-> Q')]
        for aliases, expected in groups:
            for symbol in aliases:
                with self.subTest(symbol=symbol):
                    formula = symbol + 'P' if expected == '¬P' else f'P {symbol} Q'
                    self.assertEqual(self.cli('format', formula), expected)

    def test_precedence_associativity_and_brackets(self):
        cases = {
            'P -> Q || R <-> Q && T': '(P ⇒ (Q ∨ R)) <-> (Q ∧ T)',
            'P -> Q -> R': 'P ⇒ (Q ⇒ R)',
            '(P -> Q) -> R': '(P ⇒ Q) ⇒ R',
            '~P & Q | R': '(¬P ∧ Q) ∨ R',
            '[P | Q] & R': '(P ∨ Q) ∧ R',
            'Alpha -> Beta': 'Alpha ⇒ Beta',
            '~~P': '¬¬P',
        }
        for source, expected in cases.items():
            with self.subTest(source=source):
                self.assertEqual(self.cli('format', source), expected)
                self.assertEqual(self.cli('format', expected), expected)

    def test_multiple_arguments(self):
        self.assertEqual(self.cli('format', 'P', '~Q', 'P -> Q').splitlines(),
                         ['P', '¬Q', 'P ⇒ Q'])
        self.assertEqual(self.cli('polish', 'P & Q', '~(P | Q)', 'P -> Q -> R').splitlines(),
                         ['∧PQ', '¬∨PQ', '⇒P⇒QR'])

    def check_argument(self, premises, conclusion):
        out = self.cli('prove', *(render(f) for f in [*premises, conclusion]))
        valid = is_valid(premises, conclusion)
        self.assertEqual('Countermodel:' not in out, valid, out)
        if valid:
            lines = [line.strip('`') for line in out.splitlines() if line.strip('`').strip()]
            self.assertTrue(lines, 'Empty proof')
            final = re.fullmatch(r'\s*\d+\s*\| ([^|]+) \[[^\]]+\]', lines[-1])
            self.assertIsNotNone(final, f'Expected a final, outer-scope proof line: {out}')
            self.assertEqual(final.group(1).strip(), self.cli('format', render(conclusion)))
        else:
            pairs = re.findall(r'`([^`:\n]+): (true|false)`', out)
            self.assertEqual(len(pairs), len(dict(pairs)), 'Duplicate countermodel assignments')
            values = {name: value == 'true' for name, value in pairs}
            names = set().union(*(atom_names(f) for f in [*premises, conclusion]))
            self.assertEqual(set(values), names, out)
            self.assertTrue(all(evaluate(p, values) for p in premises), out)
            self.assertFalse(evaluate(conclusion, values), out)

    def test_prover_against_truth_tables(self):
        # Fixed, bounded inputs keep execution reproducible and fast.
        forms = ['P', ('not', 'P')]
        for op in ['and', 'or', 'imp', 'iff']:
            for a, b in itertools.product(['P', 'Q'], repeat=2):
                forms.append((op, a, b))
        forms += [('or', 'P', ('not', 'P')), ('not', ('and', 'P', ('not', 'P'))),
                  ('iff', ('imp', 'P', 'Q'), ('or', ('not', 'P'), 'Q'))]
        for f in forms:
            with self.subTest(formula=render(f)):
                self.check_argument([], f)

    def test_arguments_against_truth_tables(self):
        cases = [
            (['P', ('imp', 'P', 'Q')], 'Q'),
            ([('imp', 'P', 'Q'), ('imp', 'Q', 'R')], ('imp', 'P', 'R')),
            ([('or', 'P', 'Q'), ('not', 'P')], 'Q'),
            (['P', ('not', 'P')], 'Q'),
            (['P'], 'P'),
            ([('iff', 'P', 'Q'), 'P'], 'Q'),
            ([('imp', 'P', 'Q'), 'Q'], 'P'),
            ([('imp', 'P', 'Q'), ('not', 'P')], ('not', 'Q')),
            (['P'], 'Q'),
            ([('or', 'P', 'Q')], ('and', 'P', 'Q')),
        ]
        for premises, conclusion in cases:
            with self.subTest(premises=premises, conclusion=conclusion):
                self.check_argument(premises, conclusion)

    @unittest.expectedFailure
    def test_known_defect_invalid_premise_is_not_silently_dropped(self):
        out = self.cli('prove', 'P &', 'Q -> Q')
        self.assertRegex(out.lower(), r'error|invalid|could not parse')

    @unittest.expectedFailure
    def test_known_defect_invalid_format_input_reports_error(self):
        out = self.cli('format', 'P &')
        self.assertRegex(out.lower(), r'error|invalid|could not parse')


if __name__ == '__main__':
    unittest.main(verbosity=2)
