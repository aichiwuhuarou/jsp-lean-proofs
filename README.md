# Lean formalizations of three Justin Sun Prize problems

Complete, machine-verified Lean 4 + Mathlib formalizations of the solutions of
three problems from the [Justin Sun Prize](https://www.hejustinsun.com/prize/about)
problem bank ([TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards)):

| Problem | Original question | Answer | Proof file | Main theorems |
| --- | --- | --- | --- | --- |
| [JSP-000288](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#jsp-000288) (Erdős [#346](https://www.erdosproblems.com/346)) | Must ratios of consecutive terms of a minimal stably complete sequence with `a(n+1)/a(n) ≥ 1+ε` converge to the golden ratio `φ`? | **No** — counterexample with ratios ≥ 6/5 and two subsequential limits `φ` and `φ + 1/4` | `JSP000288.lean` | `Erdos346.jsp_000288` (literal negation of the question), `Erdos346.erdos346` (packaged witness properties) |
| [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#jsp-000301) | If two consecutive positive integers are powerful, must at least one be a perfect square? | **No** — `12167 = 23³` and `12168 = 2³·3²·13²` are consecutive, powerful, and non-square | `JSP000301.lean` | `JSP000301.answer_is_no` (negation of the question), `JSP000301.counterexample` (explicit witnesses) |
| [JSP-000598](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#jsp-000598) | Can two distinct central binomial coefficients have exactly the same prime divisors? | **Yes** — `C(174,87)` and `C(176,88)` have the same prime-divisor set | `JSP000598.lean` | `jsp598` (witnesses `n = 87`, `m = 88`), `jsp598_distinct_values`, and an independent structured proof `cbcSupp_87_eq_88_structured` |

Each theorem is a complete formal proof of the full original statement — no `sorry`,
no `admit`, no unproved assumptions standing in for proof steps.

## Building

Requirements: [elan](https://github.com/leanprover/elan), `git`, `curl`/`gzip`/`tar`,
roughly 15 GB of free disk space for the Mathlib cache. The toolchain and Mathlib
revision are pinned by `lean-toolchain` and `lake-manifest.json`:

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `06d0b85b62fb783ec4045820d43cdc05967617e5`

```bash
lake exe cache get        # downloads the prebuilt Mathlib oleans (first run only)
lake env lean JSP000301.lean   # exit code 0, no output
lake env lean JSP000598.lean   # exit code 0; prints the file's own #eval exhibits
lake env lean JSP000288.lean   # exit code 0; prints the file's own #print axioms lines
```

Successful verification = command exits with code 0. Expected console output:

- `JSP000301.lean`: none.
- `JSP000598.lean`: three `#eval` exhibit lines (the prime-divisor set of `C(20,10)`
  and the two 52/55-digit coefficient values).
- `JSP000288.lean`: two `#print axioms` lines (contents below).

A single file compiles in well under a minute once the cache is in place.

## Axiom audit

`#print axioms` at the pinned commit:

```
'Erdos346.erdos346' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos346.jsp_000288' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.answer_is_no' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp598' depends on axioms: [propext, Classical.choice, Quot.sound,
  cbcSupp_87._native.native_decide.ax_1_1, cbcSupp_88._native.native_decide.ax_1_1]
```

Disclosure: in `JSP000598.lean` the two numeric lemmas `cbcSupp_87` / `cbcSupp_88`
are discharged by `native_decide` (native evaluation of concrete numerals; the Lean
kernel cannot unfold the well-founded recursion of `Nat.choose` /
`Nat.primeFactorsList` at this scale). These are the auto-generated evaluation
axioms of the `native_decide` tactic, not hand-added assumptions. The same file
also contains `cbcSupp_87_eq_88_structured`, an independent structured proof of
the same equality that does not route through those two lemmas. JSP-000288 and
JSP-000301 are kernel-only and depend on nothing beyond the three standard Lean
axioms.

## Statement fidelity

`JSP000288.lean` formalizes [Erdős problem #346](https://www.erdosproblems.com/346)
term by term: deletion of an index set stands for deletion of a subsequence of terms
(equivalent for strictly increasing sequences); `subsetSums` is "sum of distinct
members"; the two deletion conditions of the original are the finite/infinite
hypotheses of `jsp_000288`; and `∃ ε > 0, ∀ n, 1 + ε ≤ a (n+1) / a n` is exactly
the original lower bound `a(n+1)/a(n) ≥ 1+ε`. The constructed witness has
ratios ≥ 6/5 (i.e. `ε = 1/5`) and subsequential limits `φ` and `φ + 1/4`,
matching the counterexample recorded in the problem bank.

`JSP000301.lean` formalizes the catalog question verbatim, with "powerful" defined
as every prime divisor `p` satisfying `p * p ∣ n`, "perfect square" as `∃ k, k * k = _`,
and positivity as `0 < a`, `0 < b`.

`JSP000598.lean` takes "same prime divisors" as equality of the supports of the
`Nat.factorization` of the two coefficients, and additionally proves the two
coefficients are distinct values.

## Attribution

- **Formalization author:** [aichiwuhuarou](https://github.com/aichiwuhuarou)
  (repository owner). The formalization proofs were developed with AI assistance
  and were machine-verified by the Lean kernel at the pinned commit; see
  [VERIFICATION.md](VERIFICATION.md) for the verification environment and audit log.
- **Mathematical solvers:** as already recorded in the problem bank (JSP-000288 and
  JSP-000598: GPT Pro, prompted by Liam Price; JSP-000301: the recorded disproof via
  the 12167/12168 counterexample). This repository claims formalization credit only
  and no solver credit.
- **Independent verifiers:** none at time of submission. Anyone can re-run the build
  instructions above at the pinned commit; pull requests with additional verification
  evidence (fresh machine, CI logs) are welcome.

## License

Apache 2.0 — see [LICENSE](LICENSE).
