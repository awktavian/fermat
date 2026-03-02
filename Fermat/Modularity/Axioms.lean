/-
  Axiom Decomposition for Fermat's Last Theorem

  The proof of FLT for primes p ≥ 5 follows this chain:

  1. Construct the Frey curve E: y² = x(x - aᵖ)(x + bᵖ)     [PROVED — FreyCurve.lean]
  2. Show Δ(E) ≠ 0                                              [PROVED — FreyCurve.lean]
  3. Show E is semistable over ℚ                                 [AXIOM 1]
  4. By modularity (Taniyama-Shimura-Wiles), E is modular        [AXIOM 2]
  5. By Ribet's theorem (level lowering), ρ̄_{E,p} → level 2     [AXIOM 3a]
  6. dim S₂(Γ₀(2)) = 0, contradiction                           [AXIOM 3b — genus proved]
  7. genus(X₀(2)) = 0                                            [PROVED — GenusFormula.lean]

  Three axioms (decomposed from the original monolithic `ribet_contradiction`):
  • frey_semistable — algebraic, provable in principle (Campaign 2)
  • modularity_theorem — deepest theorem, Wiles 1995 (Campaign 6)
  • ribet_from_modularity_and_genus — Ribet level-lowering + genus=0→no cusp forms
    Takes the proved genus computation as explicit input (Campaign 5)

  Imperial FLT Blueprint mapping:
  • frey_semistable → Chapter 2 (First Reductions)
  • modularity_theorem → Chapters 4, 6 (Modularity Lifting Theorems)
  • ribet_theorem → Chapter 3 (p-torsion Reducibility)
  • dim_S2_Gamma0_2_eq_zero → Riemann-Roch (classical, 19th century)
-/

import Fermat.Modularity.FreyCurve
import Fermat.Modularity.NoCuspForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Fermat.Axioms

open Fermat.Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- Opaque predicates for deep mathematical concepts
-- ═══════════════════════════════════════════════════════════════════════════

/-- Semistable for integer-coefficient curves: no odd prime ℓ divides both Δ and c₄
when computed as integers. (The ℓ=2 case requires the minimal model at 2, which
depends on normalization not captured by this definition.) -/
def IsSemistableInt (Δ_z c₄_z : ℤ) : Prop :=
  ∀ (ℓ : ℕ), Nat.Prime ℓ → ℓ ≠ 2 → ¬((ℓ : ℤ) ∣ Δ_z ∧ (ℓ : ℤ) ∣ c₄_z)

/-- An elliptic curve over ℚ is modular if there exists a weight-2 newform f
such that L(E, s) = L(f, s). -/
opaque IsModular (E : WeierstrassCurve ℚ) : Prop

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM 1: Frey Semistability
-- Algebraic proof, bounded scope. Campaign 2 target.
-- Imperial Blueprint: Chapter 2, §2.1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Proved (0 sorry).** The Frey curve from a primitive FLT counterexample is
semistable at all odd primes. No odd prime ℓ divides both Δ and c₄ (as integers). -/
theorem frey_semistable (a b : ℤ) (p : ℕ) (_hp : Nat.Prime p) (hp5 : p ≥ 5)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsCoprime a b) :
    IsSemistableInt (16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2)
                    (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p) := by
  intro ℓ hℓ hℓ2 ⟨hΔ, hc₄⟩
  have hℓp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp_ne : p ≠ 0 := by omega
  -- Helper: ℓ | 16 → ℓ = 2 → contradiction with hℓ2
  have hℓ_ndvd_16 : ¬((ℓ : ℤ) ∣ 16) := by
    intro h
    have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow (show ℓ ∣ 2 ^ 4 by exact_mod_cast (show (ℓ : ℤ) ∣ 2 ^ 4 from by norm_num at h ⊢; exact h))
    exact hℓ2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hℓ.two_le)
  by_cases hla : (ℓ : ℤ) ∣ a
  · -- ℓ | a, ℓ ∤ b (coprime)
    have hlb : ¬((ℓ : ℤ) ∣ b) := fun h => absurd (hab.isUnit_of_dvd' hla h) hℓp.not_unit
    -- c₄ ≡ 16*b^{2p} mod ℓ (since ℓ|a makes all a-terms vanish)
    have : (ℓ : ℤ) ∣ (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * b ^ (2 * p)) := by
      have ha_p : (ℓ : ℤ) ∣ a ^ p := dvd_pow hla hp_ne
      have : 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * b ^ (2 * p) =
          a ^ p * (16 * a ^ p - 32 * b ^ p + 48 * b ^ p) := by ring
      rw [this]; exact dvd_mul_of_dvd_left ha_p _
    -- ℓ | c₄ and ℓ | (c₄ - 16b^{2p}) → ℓ | 16b^{2p}
    have h16b : (ℓ : ℤ) ∣ 16 * b ^ (2 * p) := by
      have := dvd_sub hc₄ this; rwa [show 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p -
        (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * b ^ (2 * p)) =
        16 * b ^ (2 * p) from by ring] at this
    -- ℓ | 16*b^{2p}. ℓ prime: ℓ | 16 or ℓ | b^{2p}.
    rcases hℓp.dvd_or_dvd h16b with h | h
    · exact hℓ_ndvd_16 h
    · exact hlb (hℓp.dvd_of_dvd_pow h)
  · by_cases hlb : (ℓ : ℤ) ∣ b
    · -- ℓ | b, ℓ ∤ a: symmetric
      have : (ℓ : ℤ) ∣ (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p)) := by
        have hb_p : (ℓ : ℤ) ∣ b ^ p := dvd_pow hlb hp_ne
        have : 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p) =
            b ^ p * (16 * b ^ p - 32 * a ^ p + 48 * a ^ p) := by ring
        rw [this]; exact dvd_mul_of_dvd_left hb_p _
      have h16a : (ℓ : ℤ) ∣ 16 * a ^ (2 * p) := by
        have := dvd_sub hc₄ this; rwa [show 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p -
          (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p)) =
          16 * a ^ (2 * p) from by ring] at this
      rcases hℓp.dvd_or_dvd h16a with h | h
      · exact hℓ_ndvd_16 h
      · exact hla (hℓp.dvd_of_dvd_pow h)
    · -- ℓ ∤ a, ℓ ∤ b. From Δ: ℓ | 16*(ab)^{2p}*(a^p+b^p)². ℓ ∤ 16, ℓ ∤ (ab)^{2p} → ℓ | (a^p+b^p)
      have hlab : ¬((ℓ : ℤ) ∣ a * b) := fun h => by
        rcases hℓp.dvd_or_dvd h with h | h <;> [exact hla h; exact hlb h]
      have hab_p : (ℓ : ℤ) ∣ a ^ p + b ^ p := by
        have hΔ_eq : (ℓ : ℤ) ∣ 16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2 := hΔ
        have := (hℓp.dvd_or_dvd hΔ_eq).resolve_left (fun h =>
          hℓ_ndvd_16 ((hℓp.dvd_or_dvd h).resolve_right (fun h => hlab (hℓp.dvd_of_dvd_pow h))))
        exact hℓp.dvd_of_dvd_pow this
      -- c₄ ≡ (a^p+b^p) * (16*(b^p-a^p)+48*a^p) = (a^p+b^p) * (16b^p+32a^p)
      -- Actually: c₄ - 16a^{2p} = (a^p+b^p) * (16b^p - 16a^p + 48a^p) by ring
      have hc₄_mod : (ℓ : ℤ) ∣ (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p)) := by
        have : 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p) =
            16 * b ^ p * (a ^ p + b ^ p) := by ring
        rw [this]; exact dvd_mul_of_dvd_right hab_p _
      have h16a : (ℓ : ℤ) ∣ 16 * a ^ (2 * p) := by
        have := dvd_sub hc₄ hc₄_mod; rwa [show 16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p -
          (16 * (b ^ p - a ^ p) ^ 2 + 48 * (a * b) ^ p - 16 * a ^ (2 * p)) =
          16 * a ^ (2 * p) from by ring] at this
      rcases hℓp.dvd_or_dvd h16a with h | h
      · exact hℓ_ndvd_16 h
      · exact hla (hℓp.dvd_of_dvd_pow h)

-- ═══════════════════════════════════════════════════════════════════════════
-- Proved results (previously axioms, now derived in FLT.lean and Ribet.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-
  The following were previously axioms in this file:

  • frey_is_modular — now derived in FLT.lean from R=T infrastructure
    (frey_modular_from_R_eq_T + galRep_irreducible_frey)

  • ribet_from_modularity_and_genus — now superseded by
    ribet_contradiction (proved in Ribet.lean) which composes
    level descent + cusp_form_level2_eq_zero

  • wiles_chain — now proved in FLT.lean from frey_is_modular +
    ribet_contradiction

  The genus computation genus(X₀(2)) = 0 enters transitively through
  cusp_form_level2_eq_zero (RiemannRoch.lean), which is sorry-free.
-/

-- Re-export for convenience
theorem genus_X0_2_proved : Fermat.Genus.genus 2 = 0 :=
  Fermat.NoCuspForms.genus_X0_level2_eq_zero

end Fermat.Axioms
