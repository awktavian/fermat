/-
  Fermat's Last Theorem — Shared Infrastructure

  Helper lemmas for power residues, divisibility, and modular arithmetic
  used across multiple FLT proofs.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace Fermat

/-- FLT statement for a specific exponent n. -/
def FermatLastTheorem (n : ℕ) : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- FLT Case I: the exponent p does not divide any of a, b, c. -/
def FLT_CaseI (p : ℕ) : Prop :=
  ∀ a b c : ℤ, ¬((p : ℤ) ∣ a) → ¬((p : ℤ) ∣ b) → ¬((p : ℤ) ∣ c) →
    a ^ p + b ^ p ≠ c ^ p

/-- If a^p + b^p = c^p has no solution in Case I and Case II,
    then FLT holds for exponent p. -/
theorem flt_from_cases (p : ℕ) (_hp : Nat.Prime p) (_hp2 : p ≥ 3)
    (hI : FLT_CaseI p)
    (hII : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ((p : ℤ) ∣ a) ∨ ((p : ℤ) ∣ b) ∨ ((p : ℤ) ∣ c) →
      a ^ p + b ^ p ≠ c ^ p) :
    FermatLastTheorem p := by
  intro a b c ha hb hc h
  by_cases hdvd : ((p : ℤ) ∣ a) ∨ ((p : ℤ) ∣ b) ∨ ((p : ℤ) ∣ c)
  · exact hII a b c ha hb hc hdvd h
  · push_neg at hdvd
    exact hI a b c hdvd.1 hdvd.2.1 hdvd.2.2 h

end Fermat
