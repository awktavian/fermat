/-
  Fermat's Last Theorem — Main Proof

  Assembles FLT for all n ≥ 3 from:
  • n = 3: mathlib (fermatLastTheoremThree)
  • n = 4: mathlib (fermatLastTheoremFour)
  • n = prime p ≥ 5: Ribet contradiction (modularity + level lowering + genus = 0)
  • n = composite: reduction to prime factor

  The proof composes:
  1. Modularity of the Frey curve (derived from R=T infrastructure)
  2. Ribet's contradiction (proved from finer axioms in Ribet.lean)

  Previously, frey_is_modular and ribet_from_modularity_and_genus were
  monolithic axioms. Now both are theorems:
  • frey_is_modular: derived from R_iso_T + R_iso_T_implies_modularity +
    galRep_irreducible_frey (Mazur)
  • ribet_contradiction: proved from level descent + cusp_form_level2_eq_zero
-/

import Fermat.Basic
import Fermat.Modularity.Axioms
import Fermat.Modularity.Ribet
import Fermat.Modularity.DeformationRing
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

namespace Fermat.FLT

open Fermat.Modularity Fermat.Axioms

theorem our_flt_iff_mathlib (n : ℕ) :
    Fermat.FermatLastTheorem n ↔ FermatLastTheoremWith ℤ n := Iff.rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- Modularity of the Frey curve (derived from R=T)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem.** The Frey curve is modular.

Derived from the R = T infrastructure:
1. galRep_irreducible_frey (Mazur): the Frey representation is irreducible
2. R_iso_T: the universal deformation ring is isomorphic to the Hecke algebra
3. R_iso_T_implies_modularity: R = T implies the curve is modular

Previously axiomatized as `frey_is_modular` in Axioms.lean. -/
private theorem frey_is_modular (a b c : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsModular (freyCurve a b p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact (Fermat.frey_modular_from_R_eq_T a b p hp5
    (galRepOfCurve (freyCurve a b p) p)
    (galRep_irreducible_frey a b c p hp5 heq ha hb hc)) 0

-- ═══════════════════════════════════════════════════════════════════════════
-- The Wiles chain (proved from finer axioms)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (Wiles, 1995).** FLT for primes p ≥ 5.

Composes:
1. frey_is_modular (derived from R=T above)
2. ribet_contradiction (proved in Ribet.lean from level descent + genus formula)

Previously used monolithic axioms frey_is_modular + ribet_from_modularity_and_genus.
Now both sides are proved from finer axioms. -/
theorem wiles_chain (a b c : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : False :=
  Fermat.ribet_contradiction a b c p hp hp5 heq ha hb hc
    (frey_is_modular a b c p hp hp5 heq ha hb hc)

-- ═══════════════════════════════════════════════════════════════════════════
-- FLT for all exponents
-- ═══════════════════════════════════════════════════════════════════════════

/-- FLT for a single prime p ≥ 3, via Wiles chain (p ≥ 5) or mathlib (p = 3). -/
theorem flt_prime (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    Fermat.FermatLastTheorem p := by
  rw [our_flt_iff_mathlib, ← fermatLastTheoremFor_iff_int]
  by_cases hp5 : p ≥ 5
  · rw [fermatLastTheoremFor_iff_int]
    intro a b c ha hb hc heq
    exact wiles_chain a b c p hp hp5 heq ha hb hc
  · have hp3' : p = 3 := by
      have h2 := hp.two_le; have : p = 3 ∨ p = 4 := by omega
      rcases this with rfl | rfl
      · rfl
      · exfalso; revert hp; decide
    rw [hp3']; exact fermatLastTheoremThree

/-- **Fermat's Last Theorem.** For all n ≥ 3, aⁿ + bⁿ = cⁿ has no nonzero integer solutions. -/
theorem flt_all_exponents (n : ℕ) (hn : n ≥ 3) :
    Fermat.FermatLastTheorem n := by
  rw [our_flt_iff_mathlib, ← fermatLastTheoremFor_iff_int]
  by_cases h4 : 4 ∣ n
  · exact FermatLastTheoremFor.mono h4 fermatLastTheoremFour
  · have hn1 : n ≠ 1 := by omega
    set p := n.minFac with hp_def
    have hp_prime : Nat.Prime p := Nat.minFac_prime hn1
    have hp_dvd : p ∣ n := Nat.minFac_dvd n
    by_cases hp2 : p = 2
    · rw [hp2] at hp_dvd
      obtain ⟨m, rfl⟩ := hp_dvd
      have hm : m ≥ 2 := by omega
      have hm_odd : ¬ 2 ∣ m := by intro ⟨k, hk⟩; apply h4; exact ⟨k, by omega⟩
      have hm1 : m ≠ 1 := by omega
      set q := m.minFac
      have hq_prime : Nat.Prime q := Nat.minFac_prime hm1
      have hq_dvd_m : q ∣ m := Nat.minFac_dvd m
      have hq_ne2 : q ≠ 2 := by intro h; rw [h] at hq_dvd_m; exact hm_odd hq_dvd_m
      have hq_ge3 : q ≥ 3 := by have := hq_prime.two_le; omega
      have hq_dvd_n : q ∣ 2 * m := dvd_mul_of_dvd_right hq_dvd_m 2
      apply FermatLastTheoremFor.mono hq_dvd_n
      rw [fermatLastTheoremFor_iff_int]; exact flt_prime q hq_prime hq_ge3
    · have hp_ge3 : p ≥ 3 := by have := hp_prime.two_le; omega
      apply FermatLastTheoremFor.mono hp_dvd
      rw [fermatLastTheoremFor_iff_int]; exact flt_prime p hp_prime hp_ge3

end Fermat.FLT
