/-
  Discriminant Infrastructure for the Frey Curve (WP-UNRAM / WP-COND)

  Computes the discriminant of the Frey curve explicitly and proves
  key divisibility properties that are intermediate steps toward:
  • `frey_rep_unramified` (Ribet.lean:115) — the mod-p Galois representation
    is unramified at odd primes dividing the conductor
  • `frey_conductor_eq` (Conductor.lean:105) — the Artin conductor equals
    the radical of |abc|

  ## What this file proves

  1. The Weierstrass discriminant Δ of the Frey curve y² = x(x - aᵖ)(x + bᵖ)
     factors as 16 · (ab)^{2p} · (a^p + b^p)² (over ℚ).

  2. Under the Fermat equation a^p + b^p = c^p, this simplifies to
     Δ = 16 · (abc)^{2p}.

  3. For any odd prime ℓ, the ℓ-adic valuation v_ℓ(Δ) = 2p · v_ℓ(|abc|).
     Since p ≥ 5, we get p | v_ℓ(Δ).

  4. An odd prime ℓ divides the integer discriminant iff ℓ divides abc.

  ## Why these matter

  The implication "p | v_ℓ(Δ) → mod-p representation unramified at ℓ"
  follows from the Tate parametrization at primes of multiplicative reduction:

  At an odd prime ℓ where the Frey curve has bad reduction (necessarily
  multiplicative, by semistability), the Tate uniformization gives
  E(Q̄_ℓ) ≅ Q̄_ℓˣ / q^ℤ where q is the Tate parameter with v_ℓ(q) = v_ℓ(Δ).
  The inertia group I_ℓ acts on E[p] through a character of order dividing
  v_ℓ(Δ). When p | v_ℓ(Δ), this character is trivial mod p, making ρ̄_{E,p}
  unramified at ℓ.

  This step requires the Tate parametrization (deep analytic/formal geometry)
  and is why `frey_rep_unramified` remains an axiom. The lemmas here are the
  *algebraic* half — the discriminant computation that feeds into it.

  For the conductor: a semistable curve has conductor = ∏{bad primes} ℓ = rad(Δ).
  Since Δ = 16(abc)^{2p}, the odd part of rad(Δ) = rad(|abc|) = freyConductor.
  The equality `conductorOf p ρ = freyConductor a b c` additionally requires
  the theory of Artin conductors for semistable curves, which is why
  `frey_conductor_eq` also remains an axiom.

  Imperial FLT Blueprint: Chapter 3, §3.2 (local analysis at bad primes).
-/

import Fermat.GaloisRep.Conductor
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option linter.dupNamespace false

namespace Fermat.Discriminant

open Finset Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Integer Discriminant of the Frey Curve
-- ═══════════════════════════════════════════════════════════════════════════

/-- The integer discriminant of the Frey curve, as a formula in a, b, p.

For the Frey curve y² = x(x - aᵖ)(x + bᵖ) in Weierstrass form
with a₁ = a₃ = a₆ = 0, a₂ = bᵖ - aᵖ, a₄ = -(ab)ᵖ, we compute:
  b₂ = 4(bᵖ - aᵖ), b₄ = -2(ab)ᵖ, b₆ = 0, b₈ = -(ab)^{2p}
  Δ = -b₂²b₈ - 8b₄³ = 16(bᵖ - aᵖ)²(ab)^{2p} + 64(ab)^{3p}
    = 16(ab)^{2p}[(bᵖ - aᵖ)² + 4(ab)ᵖ]
    = 16(ab)^{2p}(aᵖ + bᵖ)²
-/
def freyDiscriminantInt (a b : ℤ) (p : ℕ) : ℤ :=
  16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2

/-- Under the Fermat equation a^p + b^p = c^p, the integer discriminant
simplifies to 16 · (abc)^{2p}. -/
def freyDiscriminantFermat (a b c : ℤ) (p : ℕ) : ℤ :=
  16 * (a * b * c) ^ (2 * p)

/-- The Fermat equation a^p + b^p = c^p implies the discriminant factorization. -/
theorem frey_disc_fermat_eq (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    freyDiscriminantInt a b p = freyDiscriminantFermat a b c p := by
  unfold freyDiscriminantInt freyDiscriminantFermat
  rw [heq]
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Natural Number Discriminant (for padicValNat)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The natural number form of the Frey discriminant: |Δ| = 16 · |abc|^{2p}.
Uses natAbs to move to ℕ where padicValNat is defined. -/
def freyDiscNat (a b c : ℤ) (p : ℕ) : ℕ :=
  16 * (a.natAbs * b.natAbs * c.natAbs) ^ (2 * p)

theorem frey_disc_nat_eq (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    (freyDiscriminantInt a b p).natAbs = freyDiscNat a b c p := by
  rw [frey_disc_fermat_eq a b c p heq]
  unfold freyDiscriminantFermat freyDiscNat
  simp only [Int.natAbs_mul, Int.natAbs_pow]
  norm_num

theorem frey_disc_nat_ne_zero (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    freyDiscNat a b c p ≠ 0 := by
  unfold freyDiscNat
  apply mul_ne_zero
  · norm_num
  · apply pow_ne_zero
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. p-Adic Valuation of the Discriminant
-- ═══════════════════════════════════════════════════════════════════════════

/-- The ℓ-adic valuation of 16 = 2⁴ is zero for any odd prime ℓ. -/
theorem padicValNat_16_eq_zero (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    padicValNat ℓ 16 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have hℓp : Nat.Prime ℓ := Fact.out
  have : ℓ ∣ 2 := hℓp.dvd_of_dvd_pow (show ℓ ∣ 2 ^ 4 by norm_num; exact h)
  exact hℓ2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hℓp.two_le)

/-- The ℓ-adic valuation of the Frey discriminant 16 · |abc|^{2p} at an
odd prime ℓ is exactly 2p · v_ℓ(|abc|).

This is the key computation: for odd ℓ, v_ℓ(16) = 0, and
v_ℓ(|abc|^{2p}) = 2p · v_ℓ(|abc|) by standard p-adic valuation properties. -/
theorem padicVal_frey_disc (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    padicValNat ℓ (freyDiscNat a b c p) =
      2 * p * padicValNat ℓ (a.natAbs * b.natAbs * c.natAbs) := by
  unfold freyDiscNat
  have habc : a.natAbs * b.natAbs * c.natAbs ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc
  rw [padicValNat.mul (by norm_num) (pow_ne_zero _ habc)]
  rw [padicValNat_16_eq_zero ℓ hℓ2]
  rw [padicValNat.pow _ habc]
  ring

/-- **Key divisibility**: p divides the ℓ-adic valuation of the Frey
discriminant at every odd prime ℓ.

This is the algebraic core of the `frey_rep_unramified` axiom:
  v_ℓ(Δ) = 2p · v_ℓ(|abc|), so p | v_ℓ(Δ).

The implication "p | v_ℓ(Δ) → ρ̄_{E,p} unramified at ℓ" requires the
Tate parametrization, which is why the axiom remains. But this lemma
is the algebraic half that is fully proved. -/
theorem p_dvd_padicVal_frey_disc (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    p ∣ padicValNat ℓ (freyDiscNat a b c p) := by
  rw [padicVal_frey_disc a b c p ha hb hc ℓ hℓ2]
  exact ⟨2 * padicValNat ℓ (a.natAbs * b.natAbs * c.natAbs), by ring⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Odd Primes Dividing the Discriminant ↔ Dividing abc
-- ═══════════════════════════════════════════════════════════════════════════

/-- An odd prime ℓ divides the Frey discriminant iff ℓ divides abc. -/
theorem odd_prime_dvd_frey_disc_iff (a b c : ℤ) (p : ℕ)
    (hp : p ≥ 1)
    (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2) :
    ℓ ∣ freyDiscNat a b c p ↔ ℓ ∣ a.natAbs * b.natAbs * c.natAbs := by
  constructor
  · intro h
    unfold freyDiscNat at h
    have hℓp : Prime ℓ := Nat.Prime.prime hℓ
    rcases hℓp.dvd_or_dvd h with h16 | hpow
    · exfalso
      have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow
        (show ℓ ∣ 2 ^ 4 by norm_num; exact h16)
      exact hℓ2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hℓ.two_le)
    · exact hℓ.dvd_of_dvd_pow hpow
  · intro h
    unfold freyDiscNat
    have hp2 : 2 * p ≠ 0 := by omega
    exact dvd_mul_of_dvd_right (dvd_pow h hp2) 16

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Radical Lemmas
-- ═══════════════════════════════════════════════════════════════════════════

/-- A prime divides radical(n) iff it divides n (for n ≠ 0). -/
theorem prime_dvd_radical_iff {n : ℕ} (hn : n ≠ 0)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) :
    ℓ ∣ radical n ↔ ℓ ∣ n := by
  constructor
  · intro h
    exact dvd_trans h (radical_dvd hn)
  · intro h
    unfold radical
    exact Finset.dvd_prod_of_mem id
      (Nat.Prime.mem_primeFactors hℓ h hn)

/-- An odd prime divides the freyConductor iff it divides |abc|. -/
theorem odd_prime_dvd_freyConductor_iff (a b c : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    ℓ ∣ freyConductor a b c ↔ ℓ ∣ a.natAbs * b.natAbs * c.natAbs := by
  unfold freyConductor
  exact prime_dvd_radical_iff (by
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc) hℓ

/-- The odd primes dividing the Frey discriminant are exactly those
dividing the freyConductor. This is the algebraic equivalence that
underlies the conductor computation. -/
theorem odd_prime_dvd_disc_iff_dvd_conductor (a b c : ℤ) (p : ℕ)
    (hp : p ≥ 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2) :
    ℓ ∣ freyDiscNat a b c p ↔ ℓ ∣ freyConductor a b c := by
  rw [odd_prime_dvd_frey_disc_iff a b c p hp ha hb hc ℓ hℓ hℓ2]
  rw [odd_prime_dvd_freyConductor_iff a b c ha hb hc ℓ hℓ]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Roadmap — What Remains for Axiom Elimination
-- ═══════════════════════════════════════════════════════════════════════════

/-
  ## Summary of proved infrastructure

  PROVED (this file):
  • frey_disc_fermat_eq — Δ = 16(abc)^{2p} under Fermat equation
  • padicVal_frey_disc — v_ℓ(Δ) = 2p · v_ℓ(|abc|) for odd ℓ
  • p_dvd_padicVal_frey_disc — p | v_ℓ(Δ) for odd ℓ
  • odd_prime_dvd_frey_disc_iff — ℓ | Δ ↔ ℓ | abc (odd ℓ)
  • odd_prime_dvd_disc_iff_dvd_conductor — ℓ | Δ ↔ ℓ | freyConductor (odd ℓ)

  ## Axiom: frey_rep_unramified (Ribet.lean:115)

  To eliminate this axiom, one needs:

  1. [PROVED HERE] p | v_ℓ(Δ) for every odd prime ℓ dividing abc.

  2. [REQUIRES INFRASTRUCTURE] The Tate parametrization at primes of
     multiplicative reduction. This gives: for a semistable curve E/ℚ_ℓ
     with multiplicative reduction, the inertia representation
     ρ̄_{E,p}|_{I_ℓ} factors through a character of order | v_ℓ(Δ).

  3. [FOLLOWS FROM 1+2] When p | v_ℓ(Δ), the inertia character has
     order dividing v_ℓ(Δ)/p... no. More precisely: the inertia acts
     via the unramified character ψ where ψ(Frob_ℓ) = ℓ^{v_ℓ(Δ)},
     and the mod-p reduction is trivial when p | v_ℓ(Δ).

  Missing Lean infrastructure for step 2:
  • Formal groups / Tate curve over ℤ_ℓ[[q]]
  • Néron model theory (semistable → multiplicative reduction)
  • Local class field theory (inertia group structure)
  • Connection between formal group and mod-p representation

  Estimated difficulty: HARD. This is graduate-level algebraic geometry.
  The Tate curve is in Mathlib (EllipticCurve.Tate) but without the
  connection to Galois representations.

  ## Axiom: frey_conductor_eq (Conductor.lean:105)

  To eliminate this axiom, one needs:

  1. [PROVED HERE] The set of odd primes dividing Δ equals the set of
     odd primes dividing freyConductor.

  2. [REQUIRES INFRASTRUCTURE] For a semistable curve, the Artin
     conductor N_E = ∏_{bad primes ℓ} ℓ^{f_ℓ} where f_ℓ = 1
     (multiplicative reduction has conductor exponent 1 for semistable).

  3. [FOLLOWS FROM 1+2] conductorOf = ∏_{ℓ | Δ, ℓ odd} ℓ · (2-part)
     = rad_odd(Δ) · (2-part) = freyConductor · (2-part adjustment).

  Missing Lean infrastructure for step 2:
  • Artin conductor definition matching `conductorOf` opaque
  • Proof that semistable ⟹ conductor exponent ∈ {0, 1}
  • Ogg-Saito formula connecting minimal discriminant and conductor

  Estimated difficulty: MEDIUM. Primarily definitional unwinding once
  the Artin conductor is concretized, but requires minimal model theory.

  ## Recommended next steps (future sessions)

  Priority 1: Concretize `IsUnramifiedAt` (task #19).
    Define using `inertiaGroup` if available in Mathlib, or
    as v_ℓ(conductor) = 0 (equivalent for our purpose).

  Priority 2: State and prove "semistable + p | v_ℓ(Δ) → unramified at ℓ"
    as an axiom WEAKER than frey_rep_unramified but more mathematically
    transparent.

  Priority 3: Investigate Mathlib's EllipticCurve.Tate for Tate curve
    infrastructure that could help eliminate step 2.
-/

end Fermat.Discriminant
