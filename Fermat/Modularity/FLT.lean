/-
  Fermat's Last Theorem — Main Proof

  Assembles FLT for all n ≥ 3 from:
  • n = 3: mathlib (fermatLastTheoremThree)
  • n = 4: mathlib (fermatLastTheoremFour)
  • n = prime p ≥ 5: Wiles chain (three axioms composed in Axioms.lean)
  • n = composite: reduction to prime factor
-/

import Fermat.Basic
import Fermat.Modularity.Axioms
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

namespace Fermat.FLT

open Fermat.Modularity Fermat.Axioms

theorem our_flt_iff_mathlib (n : ℕ) :
    Fermat.FermatLastTheorem n ↔ FermatLastTheoremWith ℤ n := Iff.rfl

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

/-- **Fermat's Last Theorem.** For all n ≥ 3, aⁿ + bⁿ = cⁿ has no nonzero integer solutions.
Proved modulo three axioms: Frey semistability, modularity theorem, Ribet's level-lowering. -/
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
