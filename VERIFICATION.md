# Machine verification record

## What was verified

On 2026-09-17 all three proof files in this repository were compiled with
`lake env lean <file>` in the environment below. Results:

| File | Exit code | Output | `sorry` warnings |
| --- | --- | --- | --- |
| `JSP000301.lean` | 0 | none | none |
| `JSP000598.lean` | 0 | three `#eval` exhibit lines (values match the file's comments) | none |
| `JSP000288.lean` | 0 | two `#print axioms` lines (quoted in README) | none |

Axiom audit via `#print axioms` (for JSP-000301 and JSP-000598 run on temporary
copies with the audit lines appended; JSP-000288 has them built in):

- `JSP000301.counterexample`, `JSP000301.answer_is_no`:
  `[propext, Classical.choice, Quot.sound]`
- `Erdos346.erdos346`, `Erdos346.jsp_000288`:
  `[propext, Classical.choice, Quot.sound]`
- `jsp598`: `[propext, Classical.choice, Quot.sound,` two `native_decide`
  evaluation axioms from `cbcSupp_87` / `cbcSupp_88` (see README disclosure).

No `sorryAx` appears in any main theorem.

## Environment

| Item | Value |
| --- | --- |
| OS | Windows 10 22631 x64 |
| Toolchain | `leanprover/lean4:v4.35.0-rc2` via elan 4.2.4 |
| Mathlib | `06d0b85b62fb783ec4045820d43cdc05967617e5` (pinned by `lake-manifest.json`, fetched with `lake exe cache get`, 8915 cached files) |
| Command | `lake env lean <file>` per file |

Per-file wall time was 18–35 s with a warm Mathlib cache.

## Provenance of the verification runs

The three files in this repository are byte-identical copies of the files that
produced the results above (renamed from the hyphenated working names
`JSP-000301.lean`/`JSP-000598.lean`/`JSP-000288.lean`, which are not valid Lean
module names, to `JSP000301.lean`/`JSP000598.lean`/`JSP000288.lean`) and were
recompiled under the new names with the same results before the commit referenced
by the problem bank was created.
