/-
JSP-000301 · Number theory / Powerful numbers
=============================================

Problem (verbatim from the official catalog):
  "If two consecutive positive integers are powerful, must at least one
  be a perfect square?"

A positive integer `n` is *powerful* when every prime divisor `p` of `n`
satisfies `p^2 | n` — equivalently, when every prime occurs in the
factorization of `n` with exponent at least 2.

Official status: Solved (disproved).  Counterexample:

    12167 = 23 ^ 3
    12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2

These two numbers are consecutive, both powerful, and neither is a
perfect square, since 110 ^ 2 = 12100 < 12167 < 12168 < 12321 = 111 ^ 2,
and the only perfect square in [12100, 12321) is 12100 itself.

This file formalizes that disproof in Lean 4 + Mathlib.

WARNING: this is an *uncompiled static draft*.  No Lean toolchain was
available on the authoring machine; the code has only been reviewed by
hand against the Mathlib API.  See REPORT.md for a risk assessment and
for the exact patches that may be needed for the few APIs whose current
signatures could not be confirmed offline.
-/

import Mathlib

namespace JSP000301

/-! ## Definition -/

/-- A natural number `n` is **powerful** if every prime divisor `p` of `n`
satisfies `p * p | n`.

Equivalently (equivalence not needed in this file): every prime exponent
in `n.factorization` is at least `2`.  Both `12167 = 23 ^ 3` and
`12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` satisfy this with exponents `3` and
`3, 2, 2` respectively. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p * p ∣ n

/-! ## Auxiliary lemmas -/

/-- Single point of dependence on `Nat.Prime.dvd_mul`:
a prime dividing a product divides one of the factors.

PORTABILITY NOTE: this draft assumes `Nat.Prime.dvd_mul` is stated as an
implication (`p ∣ m * n → p ∣ m ∨ p ∣ n`).  If in your Mathlib version it
is an iff (`p ∣ m * n ↔ p ∣ m ∨ p ∣ n`), change the proof line to
`exact hp.dvd_mul.mp h`. -/
private theorem prime_dvd_mul_split {p m n : ℕ} (hp : p.Prime)
    (h : p ∣ m * n) : p ∣ m ∨ p ∣ n := by
  exact hp.dvd_mul.mp h

/-- A prime divisor of a prime equals that prime.

PORTABILITY NOTE: this draft assumes `Nat.dvd_prime` is stated as
`Nat.dvd_prime (hp : p.Prime) : n ∣ p → n = 1 ∨ n = p` (implication).  If
in your Mathlib version it is an iff, use `(Nat.dvd_prime hq).mp h`
instead of `Nat.dvd_prime hq h` below. -/
theorem prime_eq_of_prime_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with h1 | h2
  · exact absurd h1 hp.ne_one
  · exact h2

/-- If `q` is prime, `q * q ∣ N`, and the prime `p` divides `q`, then
`p * p ∣ N`.  (Used to transport `q^2 ∣ N` to `p^2 ∣ N` once we know the
prime divisor `p` of our number is equal to `q`.) -/
theorem sq_dvd_of_prime_dvd_prime {p q N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hN : q * q ∣ N) (h : p ∣ q) : p * p ∣ N := by
  have hpq : p = q := prime_eq_of_prime_dvd_prime hp hq h
  subst hpq
  exact hN

/-- No natural number `n` with `12100 ≤ n < 12321` other than `12100`
itself is a perfect square.

Indeed, if `k * k = n` then `k ≥ 110` (otherwise `k ≤ 109` gives
`k * k ≤ 109 ^ 2 = 11881 < 12100 ≤ n`) and `k ≤ 110` (otherwise `k ≥ 111`
gives `k * k ≥ 111 ^ 2 = 12321 > n`), hence `k = 110` and `n = 12100`,
contradicting `n ≠ 12100`.

Note: `109 ^ 2` and `111 ^ 2` are pre-folded to the literals `11881` and
`12321` (defeq by numeral evaluation), so that `omega` only ever sees
linear facts about the atom `k * k`. -/
theorem not_square_of_bounds {n : ℕ} (hne : n ≠ 12100) (hlow : 12100 ≤ n)
    (hhigh : n < 12321) : ∀ k : ℕ, k * k ≠ n := by
  intro k hk
  have h1 : 110 ≤ k := by
    by_contra hc
    push Not at hc
    have hc' : k ≤ 109 := by omega
    have h' : k * k ≤ 11881 := Nat.mul_le_mul hc' hc'  -- 109 ^ 2 = 11881
    omega
  have h2 : k ≤ 110 := by
    by_contra hc
    push Not at hc
    have hc' : 111 ≤ k := by omega
    have h' : 12321 ≤ k * k := Nat.mul_le_mul hc' hc'  -- 111 ^ 2 = 12321
    omega
  have hk110 : k = 110 := by omega
  rw [hk110] at hk
  norm_num at hk
  exact hne hk.symm

/-! ## The two witnesses -/

/-- `12167 = 23 ^ 3` is powerful: any prime divisor `p` of `23 * 23 * 23`
divides one of the factors, hence divides `23`, hence equals `23`; and
`23 ^ 2 ∣ 23 ^ 3 = 12167`.  (The last divisibility is checked
numerically by `decide`: `529 * 23 = 12167`.) -/
theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdvd
  have hcube : 23 * 23 * 23 = 12167 := by norm_num
  rw [← hcube] at hdvd
  rcases prime_dvd_mul_split hp hdvd with h | h
  · rcases prime_dvd_mul_split hp h with h | h
    · exact sq_dvd_of_prime_dvd_prime hp (by decide : (23 : ℕ).Prime)
        (by decide : 23 * 23 ∣ 12167) h
    · exact sq_dvd_of_prime_dvd_prime hp (by decide : (23 : ℕ).Prime)
        (by decide : 23 * 23 ∣ 12167) h
  · exact sq_dvd_of_prime_dvd_prime hp (by decide : (23 : ℕ).Prime)
      (by decide : 23 * 23 ∣ 12167) h

/-- `12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` is powerful: any prime divisor `p` of
`2 * 2 * 2 * 3 * 3 * 13 * 13` divides one of the seven factors, hence
divides one of `2, 3, 13`, hence equals `2`, `3` or `13`; and each of
`2 ^ 2 = 4`, `3 ^ 2 = 9`, `13 ^ 2 = 169` divides `12168`.  (Each final
divisibility is checked numerically by `decide`:
`12168 = 4 * 3042 = 9 * 1352 = 169 * 72`.) -/
theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdvd
  have hprod : 2 * 2 * 2 * 3 * 3 * 13 * 13 = 12168 := by norm_num
  rw [← hprod] at hdvd
  rcases prime_dvd_mul_split hp hdvd with h | h
  · rcases prime_dvd_mul_split hp h with h | h
    · rcases prime_dvd_mul_split hp h with h | h
      · rcases prime_dvd_mul_split hp h with h | h
        · rcases prime_dvd_mul_split hp h with h | h
          · rcases prime_dvd_mul_split hp h with h | h
            · exact sq_dvd_of_prime_dvd_prime hp Nat.prime_two
                (by decide : 2 * 2 ∣ 12168) h
            · exact sq_dvd_of_prime_dvd_prime hp Nat.prime_two
                (by decide : 2 * 2 ∣ 12168) h
          · exact sq_dvd_of_prime_dvd_prime hp Nat.prime_two
              (by decide : 2 * 2 ∣ 12168) h
        · exact sq_dvd_of_prime_dvd_prime hp Nat.prime_three
            (by decide : 3 * 3 ∣ 12168) h
      · exact sq_dvd_of_prime_dvd_prime hp Nat.prime_three
          (by decide : 3 * 3 ∣ 12168) h
    · exact sq_dvd_of_prime_dvd_prime hp (by decide : (13 : ℕ).Prime)
        (by decide : 13 * 13 ∣ 12168) h
  · exact sq_dvd_of_prime_dvd_prime hp (by decide : (13 : ℕ).Prime)
      (by decide : 13 * 13 ∣ 12168) h

/-- `12167` is not a perfect square: `12100 = 110 ^ 2 < 12167 < 12321 =
111 ^ 2` and `12167 ≠ 110 ^ 2`. -/
theorem not_square_12167 : ∀ k : ℕ, k * k ≠ 12167 :=
  not_square_of_bounds (by norm_num) (by norm_num) (by norm_num)

/-- `12168` is not a perfect square: `12100 = 110 ^ 2 < 12168 < 12321 =
111 ^ 2` and `12168 ≠ 110 ^ 2`. -/
theorem not_square_12168 : ∀ k : ℕ, k * k ≠ 12168 :=
  not_square_of_bounds (by norm_num) (by norm_num) (by norm_num)

/-! ## Main results -/

/-- The explicit counterexample data for JSP-000301: `12167` and `12168`
are positive, consecutive (`12168 = 12167 + 1`), powerful, and neither is
a perfect square. -/
theorem counterexample :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b = a + 1 ∧ Powerful a ∧ Powerful b ∧
      (∀ k : ℕ, k * k ≠ a) ∧ (∀ k : ℕ, k * k ≠ b) :=
  ⟨12167, 12168, by norm_num, by norm_num, by decide, powerful_12167, powerful_12168,
    not_square_12167, not_square_12168⟩

/-- **JSP-000301, answer: no.**

The statement "if two consecutive positive integers are powerful, then at
least one of them is a perfect square" is **false**: `12167 = 23 ^ 3` and
`12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` are consecutive powerful integers and
neither is a perfect square.

This theorem is the formal negation of the statement of the problem
("positive" appears as `0 < a`, `0 < b`; "perfect square" as
`∃ k, k * k = _`; "powerful" as `Powerful`). -/
theorem answer_is_no :
    ¬ ∀ a b : ℕ, 0 < a → 0 < b → b = a + 1 → Powerful a → Powerful b →
      (∃ k : ℕ, k * k = a) ∨ (∃ k : ℕ, k * k = b) := by
  intro h
  rcases h 12167 12168 (by norm_num) (by norm_num) (by decide)
      powerful_12167 powerful_12168 with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact not_square_12167 k hk
  · exact not_square_12168 k hk

end JSP000301
