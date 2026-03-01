/-
  Frey Curve Construction and FLT Logical Structure

  The Frey curve encodes a putative FLT counterexample as an elliptic curve.
  Combined with the axiom pipeline (Axioms.lean), this proves FLT for all n ≥ 3.
-/

import Fermat.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

namespace Fermat.Modularity

noncomputable def freyCurve (a b : ℤ) (p : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := (b ^ p - a ^ p : ℤ)
  a₃ := 0
  a₄ := -(a * b) ^ p
  a₆ := 0

/-- The discriminant of the Frey curve is nonzero.
    Proof: expand Δ with a₁=a₃=a₆=0, get Δ = 16(ab)^{2p}((b^p-a^p)²+4(ab)^p).
    All factors nonzero since a,b ≠ 0. -/
theorem frey_discriminant (a b c : ℤ) (p : ℕ) (_hp : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (_hc : c ≠ 0) :
    (freyCurve a b p).Δ ≠ 0 := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have habp : (a * b) ^ p ≠ 0 := pow_ne_zero _ hab
  have habpQ : ((a : ℚ) * b) ^ p ≠ 0 := by positivity
  -- Unfold Δ completely
  unfold freyCurve
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  -- After unfolding with a₁=0, a₃=0, a₆=0, many terms vanish.
  -- Goal should reduce to a polynomial in a₂ = (b^p - a^p : ℤ) and a₄ = -(ab)^p.
  -- Push all coercions inward and simplify zeros.
  push_cast
  ring_nf
  -- After ring_nf, the goal should be a concrete polynomial ≠ 0.
  -- Factor out (ab)^{2p} and show each factor nonzero.
  intro h
  -- After ring_nf, h is: b^(2p) * a^(4p) * 16 + b^(3p) * a^(3p) * 32 + b^(4p) * a^(2p) * 16 = 0
  -- Factor: 16 * (ab)^(2p) * (a^(2p) + 2*(ab)^p + b^(2p)) = 16 * (ab)^(2p) * (a^p + b^p)^2 = 0
  -- Since a^p + b^p = c^p ≠ 0 (c ≠ 0) and (ab)^(2p) ≠ 0 (a,b ≠ 0): contradiction.
  have hc_cast : ((c : ℚ) ^ p) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast _hc
  have heqQ : (a : ℚ) ^ p + (b : ℚ) ^ p = (c : ℚ) ^ p := by exact_mod_cast heq
  have habQ2 : ((a : ℚ) * b) ^ (p * 2) ≠ 0 := by positivity
  -- The polynomial h factors as 16 * (a*b)^(2p) * (a^p + b^p)^2
  -- The ring_nf expression equals 16 * (ab)^(2p) * (a^p + b^p)^2
  have hfact : ↑b ^ (p * 2) * ↑a ^ (p * 4) * 16 + ↑b ^ (p * 3) * ↑a ^ (p * 3) * 32 +
    ↑b ^ (p * 4) * ↑a ^ (p * 2) * (16 : ℚ) =
    16 * ((a : ℚ) * b) ^ (p * 2) * ((a : ℚ) ^ p + (b : ℚ) ^ p) ^ 2 := by ring
  rw [hfact] at h
  -- Now h : 16 * (ab)^(2p) * (a^p + b^p)^2 = 0
  -- Factor out: 16 ≠ 0, (ab)^(2p) ≠ 0, (a^p + b^p)^2 ≠ 0
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have habQ2 : ((a : ℚ) * b) ^ (p * 2) ≠ 0 := by positivity
  have hsq : ((a : ℚ) ^ p + (b : ℚ) ^ p) ^ 2 ≠ 0 := by
    rw [heqQ]; exact pow_ne_zero _ hc_cast
  exact absurd h (mul_ne_zero (mul_ne_zero h16 habQ2) hsq)

end Fermat.Modularity
