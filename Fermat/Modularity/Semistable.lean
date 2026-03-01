/-
  Frey Curve Semistability — Algebraic Core

  The Frey curve y² = x(x - aᵖ)(x + bᵖ) is semistable over ℚ.
  At odd primes ℓ, bad reduction is always multiplicative (nodal), never
  additive (cuspidal). This file proves the algebraic lemma underlying
  that fact:

  **Theorem.** In any field k, the cubic f(x) = x(x - A)(x + B) has a
  triple root only if A = B = 0.

  Proof sketch:
  • A triple root r forces f = (x - r)³.
  • Comparing constant terms: r³ = 0, so r = 0 (integral domain).
  • Comparing x² coefficients: B - A = 0, so B = A.
  • Comparing x coefficients: AB = 0, so A² = 0, hence A = 0.

  Consequence for the Frey curve: at an odd prime ℓ, if ℓ ∤ a or ℓ ∤ b
  (guaranteed by gcd(a,b,c) = 1), then the reduced cubic has no triple
  root, so any bad reduction is multiplicative → semistable at ℓ.

  This file builds toward replacing `frey_semistable` in Axioms.lean.
  The axiom remains for now; this is Campaign 2 infrastructure.
-/

import Fermat.Modularity.FreyCurve
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Fermat.Semistable

-- ═══════════════════════════════════════════════════════════════════════════
-- Part 1: Core algebraic lemma (works in any field)
-- ═══════════════════════════════════════════════════════════════════════════

/-- If the cubic x(x - A)(x + B) = (x - r)³ in a field (coefficient comparison),
then A = 0 and B = 0. This is the key algebraic fact: a triple root of the
Frey cubic forces both parameters to vanish.

The three hypotheses encode matching coefficients of x³ + (B-A)x² - ABx
against x³ - 3rx² + 3r²x - r³:
  • h_x2: coefficient of x²  →  B - A = -3r
  • h_x1: coefficient of x   →  -AB = 3r²
  • h_x0: constant term       →  0 = -r³
-/
theorem triple_root_forces_zero {k : Type*} [Field k]
    (A B r : k)
    (h_x2 : B - A = -3 * r)
    (h_x1 : -(A * B) = 3 * r ^ 2)
    (h_x0 : (0 : k) = -(r ^ 3)) :
    A = 0 ∧ B = 0 := by
  -- Step 1: r³ = 0, hence r = 0 in a field (which is an integral domain)
  have hr3 : r ^ 3 = 0 := by rw [eq_comm, neg_eq_zero] at h_x0; exact h_x0
  have hr : r = 0 := by
    rwa [pow_eq_zero_iff (by norm_num : 3 ≠ 0)] at hr3
  -- Step 2: Substitute r = 0 into the coefficient equations
  subst hr
  simp only [mul_zero, neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    Nat.zero_eq] at h_x2 h_x1
  -- h_x2 : B - A = 0 (i.e., B = A)
  -- h_x1 : -(A * B) = 0 (i.e., A * B = 0)
  have hBA : B = A := sub_eq_zero.mp h_x2
  have hAB : A * B = 0 := neg_eq_zero.mp h_x1
  -- Step 3: B = A and AB = 0 gives A² = 0, hence A = 0
  rw [hBA] at hAB
  have hA : A = 0 := mul_self_eq_zero.mp hAB
  exact ⟨hA, hBA ▸ hA⟩

/-- Equivalent formulation: if A and B are not both zero, then no element r
can satisfy the triple-root coefficient equations. This is the contrapositive
form used in the semistability argument. -/
theorem no_triple_root_of_nonzero {k : Type*} [Field k]
    (A B : k) (hAB : ¬(A = 0 ∧ B = 0)) :
    ∀ r : k, ¬(B - A = -3 * r ∧ -(A * B) = 3 * r ^ 2 ∧ (0 : k) = -(r ^ 3)) := by
  intro r ⟨h1, h2, h3⟩
  exact hAB (triple_root_forces_zero A B r h1 h2 h3)

-- ═══════════════════════════════════════════════════════════════════════════
-- Part 2: Application to ZMod ℓ for odd primes
-- ═══════════════════════════════════════════════════════════════════════════

/-- In ℤ/ℓℤ for a prime ℓ, if an integer a is nonzero mod ℓ, then a^p is
also nonzero mod ℓ (since ℤ/ℓℤ is a field, hence an integral domain). -/
theorem pow_ne_zero_of_ne_zero {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    (a : ZMod ℓ) (ha : a ≠ 0) (p : ℕ) (hp : p ≠ 0) :
    a ^ p ≠ 0 := by
  rwa [Ne, pow_eq_zero_iff hp]

/-- An integer whose cast to ZMod ℓ is zero is divisible by ℓ. -/
theorem zmod_eq_zero_iff_dvd {ℓ : ℕ} (a : ℤ) :
    (a : ZMod ℓ) = 0 ↔ (ℓ : ℤ) ∣ a :=
  ZMod.intCast_zmod_eq_zero_iff_dvd a ℓ

/-- If a prime ℓ divides a^p (with p ≥ 1), then ℓ divides a. -/
theorem prime_dvd_of_dvd_pow {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    {a : ℤ} {p : ℕ} (_hp : p ≥ 1) (h : (ℓ : ℤ) ∣ a ^ p) :
    (ℓ : ℤ) ∣ a :=
  (Nat.prime_iff_prime_int.mp hℓ).dvd_of_dvd_pow h

-- ═══════════════════════════════════════════════════════════════════════════
-- Part 3: The Frey cubic has no triple root at odd primes
-- ═══════════════════════════════════════════════════════════════════════════

/-- At an odd prime ℓ, if ℓ does not divide both a and b, then the Frey cubic
x(x - a^p)(x + b^p) reduced mod ℓ has no triple root.

This is the core of semistability at odd primes: bad reduction (ℓ | Δ) with
no triple root means the singular point is a node (multiplicative reduction),
not a cusp (additive reduction). -/
theorem frey_cubic_no_triple_root_zmod
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (hℓ_odd : ℓ ≠ 2)
    (a b : ℤ) (p : ℕ) (hp : p ≥ 1)
    (hab : ¬((ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b)) :
    ∀ r : ZMod ℓ,
      ¬((↑(b ^ p) : ZMod ℓ) - ↑(a ^ p) = -3 * r ∧
        -(↑(a ^ p) * ↑(b ^ p) : ZMod ℓ) = 3 * r ^ 2 ∧
        (0 : ZMod ℓ) = -(r ^ 3)) := by
  -- The ZMod ℓ images of a^p and b^p cannot both be zero,
  -- because that would require ℓ | a and ℓ | b.
  have hAB : ¬((↑(a ^ p) : ZMod ℓ) = 0 ∧ (↑(b ^ p) : ZMod ℓ) = 0) := by
    intro ⟨ha0, hb0⟩
    apply hab
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha0 hb0
    exact ⟨(Nat.prime_iff_prime_int.mp hℓ.out).dvd_of_dvd_pow ha0,
            (Nat.prime_iff_prime_int.mp hℓ.out).dvd_of_dvd_pow hb0⟩
  exact no_triple_root_of_nonzero _ _ hAB

/-- If a and b are coprime integers and a^p + b^p = c^p, then for any prime ℓ,
it is not the case that ℓ divides both a and b. -/
theorem coprime_no_common_factor
    (a b : ℤ) (hab : IsCoprime a b) (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    ¬((ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) := by
  intro ⟨hla, hlb⟩
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  exact hprime.not_unit (hab.isUnit_of_dvd' hla hlb)

-- ═══════════════════════════════════════════════════════════════════════════
-- Part 4: Combined theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Main theorem (algebraic core of semistability at odd primes).**

For a putative Fermat counterexample a^p + b^p = c^p with gcd(a,b,c) = 1
and prime p ≥ 5, the Frey cubic x(x - a^p)(x + b^p) has no triple root
in ZMod ℓ for any odd prime ℓ.

This means: at every odd prime ℓ where the Frey curve has bad reduction,
the reduction is multiplicative (node), not additive (cusp). Combined with
a separate analysis at ℓ = 2 (which uses the minimal model), this gives
full semistability. -/
theorem frey_no_additive_reduction_odd
    (a b : ℤ) (p : ℕ) (_hp : Nat.Prime p) (_hp5 : p ≥ 5)
    (hab : IsCoprime a b)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ_odd : ℓ ≠ 2) :
    ∀ r : ZMod ℓ,
      ¬((↑(b ^ p) : ZMod ℓ) - ↑(a ^ p) = -3 * r ∧
        -(↑(a ^ p) * ↑(b ^ p) : ZMod ℓ) = 3 * r ^ 2 ∧
        (0 : ZMod ℓ) = -(r ^ 3)) := by
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact frey_cubic_no_triple_root_zmod ℓ hℓ_odd a b p (by omega) (
    coprime_no_common_factor a b hab ℓ hℓ
  )

end Fermat.Semistable
