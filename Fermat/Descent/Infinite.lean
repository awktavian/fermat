/-
  Infinite Descent Framework

  Generic descent principles used across FLT proofs.
-/

import Mathlib.Tactic

namespace Fermat.Descent

/-- Infinite descent on natural numbers: if every instance of P(n) implies
    a strictly smaller instance P(m), then P never holds. -/
theorem infinite_descent {P : ℕ → Prop}
    (h : ∀ n, P n → ∃ m, m < n ∧ P m) : ∀ n, ¬P n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    obtain ⟨m, hm_lt, hm⟩ := h n hn
    exact ih m hm_lt hm

/-- Descent on integers via absolute value. -/
theorem int_descent {P : ℤ → Prop}
    (h : ∀ a, P a → ∃ a', a'.natAbs < a.natAbs ∧ P a') :
    ∀ a, ¬P a := by
  intro a hPa
  have : ¬(∃ n, ∃ x : ℤ, x.natAbs = n ∧ P x) := by
    push_neg
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxn hPx
      obtain ⟨x', hx'lt, hPx'⟩ := h x hPx
      exact ih x'.natAbs (by omega) x' rfl hPx'
  exact this ⟨a.natAbs, a, rfl, hPa⟩

end Fermat.Descent
