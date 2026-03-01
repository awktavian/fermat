/-
  Fermat's Last Theorem for Regular Primes

  Via flt-regular: FLT holds for any regular prime (p does not divide h(ℚ(ζ_p))).
  This covers all primes p < 37 (first irregular prime), proved without any axioms.

  Small numbers (3 ≤ n ≤ 16) are also covered by direct computation.
-/

import Fermat.Basic
import FltRegular.FltRegular
import FltRegular.SmallNumbers.SmallNumbers
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

namespace Fermat.RegularPrimes

/-- **Proved (sorry-free).** FLT for any regular prime, via Kummer theory.
A prime p is regular if p does not divide the class number of ℚ(ζ_p).
All primes below 37 are regular. -/
theorem flt_regular_prime (p : ℕ) [hp : Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p :=
  flt_regular hreg hodd

/-- **Proved (sorry-free).** FLT for n = 5, via regularity of 5. -/
theorem flt_five : FermatLastTheoremFor 5 := fermatLastTheoremFive

/-- **Proved (sorry-free).** FLT for n = 7, via regularity of 7. -/
theorem flt_seven : FermatLastTheoremFor 7 := fermatLastTheoremSeven

/-- **Proved (sorry-free).** FLT for n = 11, via regularity of 11. -/
theorem flt_eleven : FermatLastTheoremFor 11 := fermatLastTheoremEleven

/-- **Proved (sorry-free).** FLT for n = 13, via regularity of 13. -/
theorem flt_thirteen : FermatLastTheoremFor 13 := fermatLastTheoremThirteen

/-- **Proved (sorry-free).** FLT for all n in [3, 16]. -/
theorem flt_small (n : ℕ) (hn : n ∈ Finset.Icc 3 16) : FermatLastTheoremFor n :=
  FLT_small hn

/-- Lift FLT from ℕ (FermatLastTheoremFor) to ℤ (our FermatLastTheorem). -/
theorem flt_for_to_flt (n : ℕ) (h : FermatLastTheoremFor n) :
    Fermat.FermatLastTheorem n := by
  rw [show Fermat.FermatLastTheorem n = FermatLastTheoremWith ℤ n from rfl,
      ← fermatLastTheoremFor_iff_int]
  exact h

end Fermat.RegularPrimes
