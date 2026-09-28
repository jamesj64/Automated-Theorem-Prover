# Frosty quick regression suite

A Python standard-library black-box suite for Automated-Theorem-Prover. It builds and exercises the real F# CLI; it does not modify production source.

## Run

Requires Python 3.8+ and a .NET 8 SDK. Put this folder inside the repository, then run from the repository root:

```sh
python3 frosty-tests/test_frosty.py
```

Or keep it elsewhere and supply the repository path:

```sh
FROSTY_REPO=/absolute/path/to/Automated-Theorem-Prover python3 /absolute/path/to/frosty-tests/test_frosty.py
```

For an SDK outside PATH, set `DOTNET` to the full path of its `dotnet` executable. The first build may need network access to restore FParsec. The build has a 180-second timeout; each CLI invocation has a 10-second timeout. Normal build output is suppressed unless the build fails.

## Coverage

- Help entry points and multiple formula arguments.
- All documented operator aliases, operator precedence, right-associative implication, brackets, multi-letter atoms, double negation, and formatting round trips.
- Polish notation output.
- 21 bounded formula cases and 10 inference cases, including modus ponens, hypothetical/disjunctive syllogism, inconsistent premises, premise reiteration, biconditionals, and invalid inference patterns.
- An independent truth-table evaluator determines validity. For invalid cases, every returned countermodel must assign exactly the input atoms, satisfy all premises, and falsify the conclusion.
- Valid cases must end with the requested conclusion outside any subproof. No exact proof sequence or length is required.

This is a regression/smoke suite, not a complete proof checker: it does not independently validate every inference rule or intermediate proof line, and it does not exhaustively test formulas or performance.

## Known defects

Two tests use `unittest.expectedFailure` to explicitly document current behavior:

1. `prove` silently drops a malformed premise and can prove the remaining argument.
2. `format` silently drops malformed input instead of reporting an error.

These are proposed error-handling expectations, not assertions that the current README specifies an exact diagnostic. The tests accept several diagnostic phrases; a future feature task should define its error contract precisely. Once fixed, remove the relevant `expectedFailure` decorators. Unexpected successes cause unittest to fail, so fixes prompt an update to these markers.

This baseline suite is separate from the task-specific verifiers required by the training assignment. Those must be aligned to the final problem statement.

## Verified baseline

- Repository: https://github.com/jamesj64/Automated-Theorem-Prover
- Commit: `bf3483ebeb0d1f6e8489ebbd0195a3dc4fd5b167`
- Environment: macOS ARM64, .NET SDK 8.0.425, Python 3
- Result: 8 test methods, 6 passed and 2 expected failures; parameterized checks run as subtests.
- Test run (including build): 9.791 seconds.

See `test-results.txt` for captured output.
