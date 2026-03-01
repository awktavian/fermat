/-
  Fermat's Last Theorem for n = 5

  Complete proof via flt-regular: 5 is a regular prime (h(ℚ(ζ₅)) = 1),
  so FLT holds for exponent 5 by the Kummer-based argument.

  The Sophie Germain Case I argument (q = 11 is prime) is proved separately
  in SophieGermain.lean as an independent result.
-/

import Fermat.Basic
import Mathlib.NumberTheory.FLT.Four
import FltRegular.SmallNumbers.Five.FLT5
import Mathlib.Tactic

namespace Fermat.Five

/-- **Proved.** FLT for n = 5, via flt-regular (5 is regular, h(ℚ(ζ₅)) = 1). -/
theorem flt_five : FermatLastTheorem 5 := by
  rw [show FermatLastTheorem 5 = FermatLastTheoremWith ℤ 5 from rfl,
      ← fermatLastTheoremFor_iff_int]
  exact fermatLastTheoremFive

end Fermat.Five
