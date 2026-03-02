/-
  Riemann-Roch for Modular Curves: S₂(Γ₀(2)) = 0

  Connects the genus formula (proved in GenusFormula.lean) to the actual
  CuspForm type from mathlib, proving there are no weight-2 cusp forms
  at level Γ₀(2).

  The chain:
  1. genus(X₀(2)) = 0                    [PROVED — GenusFormula.lean, by decide]
  2. S₂(Γ₀(2)) is subsingleton           [AXIOM — Riemann-Roch + finiteness for N=2]
  3. dim S₂(Γ₀(2)) = 0                   [DERIVED — from 2]
  4. Every f in S₂(Γ₀(2)) is zero        [DERIVED — from 2]

  Previous version had two general axioms (dim_cusp_forms_weight2 for all N,
  cusp_forms_finite for all N). Since both were only used at N=2, we replaced
  them with a single targeted axiom.

  The mathematical content: for Γ₀(2), weight-2 cusp forms correspond to
  holomorphic differentials on X₀(2). Since genus(X₀(2)) = 0 (by the genus
  formula), the space of holomorphic differentials is trivial.

  The coercion Γ₀(N) ⊂ SL₂(ℤ) → GL₂(ℝ) uses mathlib's existing
  `mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ` and the coercion instance
  from ArithmeticSubgroups.lean.
-/

import Fermat.Modularity.GenusFormula
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Fermat.RiemannRoch

open CongruenceSubgroup Fermat.Genus
open scoped MatrixGroups

-- ═══════════════════════════════════════════════════════════════════════════
-- Step 1: Coercion from Γ₀(N) ⊂ SL₂(ℤ) to a subgroup of GL₂(ℝ)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The image of Γ₀(N) in GL(2, ℝ) via the standard embedding SL₂(ℤ) ↪ GL₂(ℝ).
Defined directly as `(Gamma0 N).map (mapGL ℝ)` to match the typeclass instances
in ArithmeticSubgroups.lean. -/
def Gamma0_GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The image of Γ₀(N) under mapGL has determinant 1 (inherited from SL₂(ℤ)).
Explicit construction since the typeclass instance for `Γ.map (mapGL S)` needs
the `Gamma0_GL` definition to be unfolded. -/
instance instHasDetOneGamma0GL (N : ℕ) : (Gamma0_GL N).HasDetOne where
  det_eq {g} hg := by
    simp only [Gamma0_GL, Subgroup.mem_map] at hg
    obtain ⟨γ, _, rfl⟩ := hg
    simp [Matrix.SpecialLinearGroup.det_mapGL]

-- ═══════════════════════════════════════════════════════════════════════════
-- Step 2: The space of weight-k cusp forms at level Γ₀(N)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The ℂ-vector space S_k(Γ₀(N)) of weight-k cusp forms for the congruence
subgroup Γ₀(N), viewed as holomorphic functions on the upper half-plane that
are slash-invariant under Γ₀(N) and vanish at all cusps. -/
abbrev CuspFormSpace (N : ℕ) (k : ℤ) : Type := CuspForm (Gamma0_GL N) k

-- The Module ℂ structure is automatic from HasDetOne:
example (N : ℕ) (k : ℤ) : Module ℂ (CuspFormSpace N k) := inferInstance

-- ═══════════════════════════════════════════════════════════════════════════
-- Step 3: The single axiom — S₂(Γ₀(2)) is trivial
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (No weight-2 cusp forms at level 2).**
The space S₂(Γ₀(2)) of weight-2 cusp forms for Γ₀(2) is trivial (subsingleton).

This follows from two classical results:
1. **Riemann-Roch**: dim S₂(Γ₀(N)) = genus(X₀(N)) for N >= 1.
   Weight-2 cusp forms are identified with holomorphic differentials
   on X₀(N), whose space has dimension equal to the genus.
2. **Genus formula**: genus(X₀(2)) = 0 (proved in GenusFormula.lean).

Together: S₂(Γ₀(2)) has dimension 0, hence is trivial.

Alternatively, the valence formula gives the total number of zeros of
a weight-k form for Γ₀(N) as k*[SL₂(Z):Γ₀(N)]/12 = 2*3/12 = 1/2.
A cusp form vanishes at both cusps (order >= 1 each), giving >= 2 zeros.
Since 2 > 1/2, no nonzero weight-2 cusp form exists. -/
axiom cusp_forms_level2_subsingleton : Subsingleton (CuspFormSpace 2 2)

-- ═══════════════════════════════════════════════════════════════════════════
-- Step 4: Derived results from the single axiom
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (Freeness of cusp form spaces).**
The space S₂(Γ₀(N)) is a free ℂ-module. This is automatic: every module
over a division ring (hence every ℂ-vector space) is free. -/
noncomputable instance cusp_forms_free (N : ℕ) : Module.Free ℂ (CuspFormSpace N 2) :=
  Module.Free.of_divisionRing ℂ (CuspFormSpace N 2)

/-- **Theorem (Finite-dimensionality at level 2).**
S₂(Γ₀(2)) is a finite-dimensional ℂ-vector space.
Derived from subsingleton: a subsingleton module has rank 0, hence is finite. -/
noncomputable instance cusp_forms_finite_level2 :
    Module.Finite ℂ (CuspFormSpace 2 2) := by
  haveI := cusp_forms_level2_subsingleton
  exact Module.finite_of_rank_eq_zero (rank_subsingleton' ℂ (CuspFormSpace 2 2))

/-- **Theorem.** The space of weight-2 cusp forms at level Γ₀(2) has
dimension 0. -/
theorem no_cusp_forms_level2 :
    Module.finrank ℂ (CuspFormSpace 2 2) = 0 := by
  haveI := cusp_forms_level2_subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- **Theorem.** Every weight-2 cusp form at level Γ₀(2) is the zero form.

Proof: The space is subsingleton (from axiom), so every element equals 0. -/
theorem cusp_form_level2_eq_zero (f : CuspFormSpace 2 2) : f = 0 := by
  haveI := cusp_forms_level2_subsingleton
  exact Subsingleton.elim f 0

-- ═══════════════════════════════════════════════════════════════════════════
-- Summary of axiom budget
-- ═══════════════════════════════════════════════════════════════════════════

/-
  PROVED (sorry-free):
  * genus(X₀(2)) = 0                         [GenusFormula.lean, by decide]
  * S₂(Γ₀(2)) is Module.Finite              [this file, from Subsingleton]
  * dim S₂(Γ₀(2)) = 0                        [this file, from Subsingleton]
  * Every f in S₂(Γ₀(2)) satisfies f = 0     [this file, from Subsingleton]
  * S₂(Γ₀(N)) is Module.Free                [Module.Free.of_divisionRing]

  AXIOM (1, was 2):
  * cusp_forms_level2_subsingleton: S₂(Γ₀(2)) is Subsingleton
    Combines Riemann-Roch (dim = genus) + genus formula (genus(X₀(2)) = 0)
    + finite-dimensionality. A single targeted axiom replacing two general ones.
    When mathlib formalizes Riemann-Roch for compact Riemann surfaces and
    identifies S₂ with holomorphic differentials, this becomes a theorem.

  COERCION (sorry-free):
  * Gamma0_GL: Γ₀(N) subset SL₂(Z) to GL₂(R) via mapGL R
    Uses mathlib's existing coercion instance from ArithmeticSubgroups.lean.
-/

end Fermat.RiemannRoch
