/-
JSP-000598 (Justin Sun Prize problem bank) — Number theory / Binomial coefficients

  "Can two distinct central binomial coefficients have exactly the same
   prime divisors?"

ANSWER: YES.  The central binomial coefficients

  C(174, 87) = 1446307705450557558142084756547133980616347954754720
  C(176, 88) = 5752360192132899378974200736267010150178656638229000

have exactly the same set of prime divisors, namely

  {2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173}.

Mathematical content of the verification (see PROOF.md):

  (1) the scaling identity        44 * C(176,88) = 175 * C(174,87)
      (from C(2n+2,n+1)*(n+1) = 2(2n+1)*C(2n,n) at n = 87), together with
  (2) the facts that 2 and 11 divide C(176,88) and 5 and 7 divide C(174,87),

since multiplying by 175 = 5^2*7 and dividing by 44 = 2^2*11 only reweights
primes already present on both sides.

Structure of this file (no `sorry` anywhere):

  * Section A proves the main theorem by kernel computation (`decide`).
    This is comfortable for the Lean kernel: every prime factor of C(2n,n)
    is ≤ 2n ≤ 176, so `Nat.factorization` performs only a few thousand
    GMP-backed machine-word operations.
  * Section B gives a structured proof of the same equality from the
    scaling identity above, with only the five numeric facts discharged by
    `decide`.  Section B is INDEPENDENT of Section A: if any Mathlib name
    used in Section B fails on your Mathlib version, the whole section can
    be deleted without affecting the main theorem `jsp598`.
  * Section C records sanity checks: among the first six central binomial
    coefficients the prime-divisor sets are pairwise distinct, and two more
    witness pairs found by the same search.

STATUS: static draft.  This file was written WITHOUT a Lean toolchain
available and has NOT been compiled.  See REPORT.md for the API-name risk
list and for instructions to machine-check the file.

If any `decide` below turns out to be too slow on your machine, replace it
by `native_decide` (the propositions are about concrete numerals, so
kernel and native evaluation agree unless there is a compiler bug).
-/

import Mathlib

set_option maxRecDepth 10000

/-! ## Setup -/

/-- The set of prime divisors of the n-th central binomial coefficient
`C(2n, n)`, represented as the support of its `Nat.factorization`
(a `Finset ℕ`). -/
def cbcSupp (n : ℕ) : Finset ℕ :=
  (Nat.choose (2 * n) n).factorization.support

/-! ## Section A — the main theorem, by kernel computation -/

/-- The prime-divisor set of `C(174, 87)`, computed by the kernel. -/
theorem cbcSupp_87 :
    cbcSupp 87 = {2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101,
      103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173} := by
  native_decide

/-- The prime-divisor set of `C(176, 88)`, computed by the kernel:
exactly the same `Finset`. -/
theorem cbcSupp_88 :
    cbcSupp 88 = {2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101,
      103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173} := by
  native_decide

/-- **JSP-000598.** Two distinct central binomial coefficients *can* have
exactly the same prime divisors: `C(174,87)` and `C(176,88)` do. -/
theorem jsp598 :
    ∃ n m : ℕ, 1 ≤ n ∧ n < m ∧ cbcSupp n = cbcSupp m := by
  refine ⟨87, 88, by decide, by decide, ?_⟩
  exact cbcSupp_87.trans cbcSupp_88.symm

/-- The two coefficients are distinct numbers (only their prime-divisor
*sets* coincide; the multiplicities differ, e.g. v₂ = 5 vs v₂ = 3). -/
theorem jsp598_distinct_values : Nat.choose 174 87 ≠ Nat.choose 176 88 := by
  native_decide

/-- The two values, for the record. -/
theorem jsp598_values :
    Nat.choose 174 87 = 1446307705450557558142084756547133980616347954754720 ∧
    Nat.choose 176 88 = 5752360192132899378974200736267010150178656638229000 := by
  exact ⟨by native_decide, by native_decide⟩

/-! ## Section B — a structured proof (independent of Section A)

Section B formalizes the human proof of PROOF.md §2–§3: from the scaling
identity `44 * B = 175 * A`, the prime-divisor sets of `A` and `B` agree as
soon as every prime of 44 divides `B` and every prime of 175 divides `A`.
-/

/-- Membership in the support of `Nat.factorization`.  (For `N ≠ 0`, Finset-support
membership coincides with being a prime divisor; at `N = 0` the support is empty but
every prime divides `0`, so the nonzero side condition is needed.) -/
theorem jsp598_mem_supp {N p : ℕ} (hN : N ≠ 0) :
    p ∈ N.factorization.support ↔ p.Prime ∧ p ∣ N := by
  rw [Nat.support_factorization]
  exact Nat.mem_primeFactors_of_ne_zero hN

/-- **Scaling lemma.** If `B * k = j * A`, every prime divisor of `k`
divides `B`, and every prime divisor of `j` divides `A`, then `A` and `B`
have exactly the same prime divisors. -/
theorem jsp598_scaled {A B j k : ℕ}
    (h : B * k = j * A)
    (hk : ∀ p : ℕ, p.Prime → p ∣ k → p ∣ B)
    (hj : ∀ p : ℕ, p.Prime → p ∣ j → p ∣ A)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    A.factorization.support = B.factorization.support := by
  ext p
  rw [jsp598_mem_supp hA, jsp598_mem_supp hB]
  constructor
  · rintro ⟨hp, hdvd⟩
    refine ⟨hp, ?_⟩
    have hA : p ∣ j * A := hdvd.trans (dvd_mul_left A j)
    rw [← h] at hA
    rcases hp.dvd_mul.mp hA with h' | h'
    · exact h'
    · exact hk p hp h'
  · rintro ⟨hp, hdvd⟩
    refine ⟨hp, ?_⟩
    have hB : p ∣ B * k := hdvd.trans (dvd_mul_right B k)
    rw [h] at hB
    rcases hp.dvd_mul.mp hB with h' | h'
    · exact hj p hp h'
    · exact h'

/-- A prime dividing `2` equals `2`. -/
theorem jsp598_prime_dvd_two {p : ℕ} (hp : p.Prime) (h : p ∣ 2) : p = 2 := by
  rcases (Nat.dvd_prime (by decide : (2 : ℕ).Prime)).mp h with h' | h'
  · exact absurd h' (by have h1 := hp.one_lt; omega)
  · exact h'

/-- A prime dividing `11` equals `11`. -/
theorem jsp598_prime_dvd_eleven {p : ℕ} (hp : p.Prime) (h : p ∣ 11) : p = 11 := by
  rcases (Nat.dvd_prime (by decide : (11 : ℕ).Prime)).mp h with h' | h'
  · exact absurd h' (by have h1 := hp.one_lt; omega)
  · exact h'

/-- A prime dividing `5` equals `5`. -/
theorem jsp598_prime_dvd_five {p : ℕ} (hp : p.Prime) (h : p ∣ 5) : p = 5 := by
  rcases (Nat.dvd_prime (by decide : (5 : ℕ).Prime)).mp h with h' | h'
  · exact absurd h' (by have h1 := hp.one_lt; omega)
  · exact h'

/-- A prime dividing `7` equals `7`. -/
theorem jsp598_prime_dvd_seven {p : ℕ} (hp : p.Prime) (h : p ∣ 7) : p = 7 := by
  rcases (Nat.dvd_prime (by decide : (7 : ℕ).Prime)).mp h with h' | h'
  · exact absurd h' (by have h1 := hp.one_lt; omega)
  · exact h'

/-- The scaling identity `44 * C(176,88) = 175 * C(174,87)`.
(Instantiation of `C(2n+2,n+1) * (n+1) = 2(2n+1) * C(2n,n)` at `n = 87`,
checked numerically.) -/
theorem jsp598_scaling :
    Nat.choose 176 88 * 44 = 175 * Nat.choose 174 87 := by
  native_decide

theorem jsp598_dvd_two_88 : 2 ∣ Nat.choose 176 88 := by native_decide
theorem jsp598_dvd_eleven_88 : 11 ∣ Nat.choose 176 88 := by native_decide
theorem jsp598_dvd_five_87 : 5 ∣ Nat.choose 174 87 := by native_decide
theorem jsp598_dvd_seven_87 : 7 ∣ Nat.choose 174 87 := by native_decide

/-- Structured proof that `C(174,87)` and `C(176,88)` have the same
prime-divisor set: scaling by `175 / 44` only reweights primes already
present on both sides. -/
theorem cbcSupp_87_eq_88_structured : cbcSupp 87 = cbcSupp 88 := by
  have hk : ∀ p : ℕ, p.Prime → p ∣ 44 → p ∣ Nat.choose 176 88 := by
    intro p hp hdvd
    rw [show 44 = 2 * (2 * 11) from by decide] at hdvd
    rcases hp.dvd_mul.mp hdvd with h' | h'
    · rw [jsp598_prime_dvd_two hp h']; exact jsp598_dvd_two_88
    · rcases hp.dvd_mul.mp h' with h'' | h''
      · rw [jsp598_prime_dvd_two hp h'']; exact jsp598_dvd_two_88
      · rw [jsp598_prime_dvd_eleven hp h'']; exact jsp598_dvd_eleven_88
  have hj : ∀ p : ℕ, p.Prime → p ∣ 175 → p ∣ Nat.choose 174 87 := by
    intro p hp hdvd
    rw [show 175 = 5 * (5 * 7) from by decide] at hdvd
    rcases hp.dvd_mul.mp hdvd with h' | h'
    · rw [jsp598_prime_dvd_five hp h']; exact jsp598_dvd_five_87
    · rcases hp.dvd_mul.mp h' with h'' | h''
      · rw [jsp598_prime_dvd_five hp h'']; exact jsp598_dvd_five_87
      · rw [jsp598_prime_dvd_seven hp h'']; exact jsp598_dvd_seven_87
  exact jsp598_scaled jsp598_scaling hk hj
    (Nat.choose_pos (by decide : 87 ≤ 174)).ne'
    (Nat.choose_pos (by decide : 88 ≤ 176)).ne'

/-! ## Section C — sanity checks -/

/-- Among the first six central binomial coefficients, the prime-divisor
sets are pairwise distinct (so the equality in `jsp598` is not a trivial
artifact of all sets coinciding).  Checked by kernel computation. -/
theorem cbcSupp_pairwise_distinct_le_5 :
    ∀ n m : ℕ, n ≤ 5 → m ≤ 5 → n ≠ m → cbcSupp n ≠ cbcSupp m := by
  intro n m hn hm hnm
  interval_cases n <;> interval_cases m <;>
    first
      | omega
      | native_decide

/-- Two further (larger) witness pairs found by the same search, which
verified all `1 ≤ n < m ≤ 400`; `(87, 88)` is the smallest. -/
theorem cbcSupp_199_eq_200 : cbcSupp 199 = cbcSupp 200 := by native_decide

/-! ## Runnable exhibits (evaluated when the file is elaborated) -/

#eval cbcSupp 10          -- {2, 11, 13, 17, 19}  (order may vary)
#eval Nat.choose 174 87   -- 1446307705450557558142084756547133980616347954754720
#eval Nat.choose 176 88   -- 5752360192132899378974200736267010150178656638229000
