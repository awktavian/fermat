/-
  Continuous Galois Representations (WP1)

  Defines the basic types for Galois representations used in the modularity
  lifting framework. The absolute Galois group Gal(K̄/K) acts on finite-
  dimensional vector spaces over coefficient fields k via group homomorphisms
  into GL_n(k).

  Continuity: The mathematical definition requires continuity with respect
  to the Krull topology on Gal(K̄/K) and the discrete topology on GL_n(k)
  (for ℓ-adic representations, the ℓ-adic topology). This is not yet
  enforced in the type — it will be added when the topological GL
  infrastructure is available. The types are correct; continuity is a
  future refinement, not a structural change.

  Imperial FLT Blueprint: Chapter 3 (Galois representations attached to
  elliptic curves), Chapter 4 (modularity lifting).
-/

import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod

set_option linter.dupNamespace false

namespace Fermat

open Matrix

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The Absolute Galois Group
-- ═══════════════════════════════════════════════════════════════════════════

/-- The absolute Galois group Gal(K̄/K), defined as the group of K-algebra
automorphisms of the algebraic closure of K. This is a profinite group
under the Krull topology (instance provided by mathlib). -/
abbrev AbsGaloisGroup (K : Type*) [Field K] := Field.absoluteGaloisGroup K

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Galois Representations
-- ═══════════════════════════════════════════════════════════════════════════

/-- An n-dimensional Galois representation of Gal(K̄/K) over the coefficient
field k. This is a group homomorphism ρ : Gal(K̄/K) →* GL_n(k).

In the FLT proof, the key case is n = 2 (the Tate module of an elliptic
curve gives a 2-dimensional representation). The coefficient field k is
typically 𝔽ₚ (mod-p representations) or ℚₗ (ℓ-adic representations). -/
structure GaloisRep (n : ℕ) (k : Type*) [Field k] (K : Type*) [Field K] where
  /-- The underlying group homomorphism from the absolute Galois group to GL_n(k). -/
  toMonoidHom : AbsGaloisGroup K →* GL (Fin n) k

attribute [coe] GaloisRep.toMonoidHom

namespace GaloisRep

variable {n : ℕ} {k : Type*} [Field k] {K : Type*} [Field K]

instance : CoeFun (GaloisRep n k K) (fun _ => AbsGaloisGroup K → GL (Fin n) k) where
  coe ρ := ρ.toMonoidHom

@[ext]
theorem ext {ρ₁ ρ₂ : GaloisRep n k K} (h : ∀ g, ρ₁ g = ρ₂ g) : ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; congr 1; exact MonoidHom.ext h

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Determinant Character
-- ═══════════════════════════════════════════════════════════════════════════

/-- The determinant character det ∘ ρ : Gal(K̄/K) →* kˣ.
For the mod-p representation attached to an elliptic curve E,
this is the mod-p cyclotomic character. -/
def det (ρ : GaloisRep n k K) : AbsGaloisGroup K →* kˣ :=
  GeneralLinearGroup.det.comp ρ.toMonoidHom

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Irreducibility
-- ═══════════════════════════════════════════════════════════════════════════

/-- A submodule W of k^n is invariant under ρ if every element of the
Galois group preserves W under the matrix action. -/
def IsInvariant (ρ : GaloisRep n k K) (W : Submodule k (Fin n → k)) : Prop :=
  ∀ g : AbsGaloisGroup K, ∀ v : Fin n → k, v ∈ W →
    (ρ.toMonoidHom g).val.mulVec v ∈ W

/-- A Galois representation is irreducible (absolutely irreducible) if
it has no proper nonzero invariant subspaces. Equivalently, the only
ρ-stable submodules of k^n are {0} and k^n.

This is the key hypothesis in Ribet's theorem: the mod-p representation
ρ̄_{E,p} of a semistable elliptic curve is irreducible for p ≥ 5 (by
Mazur's theorem on rational isogenies). -/
def IsIrreducible (ρ : GaloisRep n k K) : Prop :=
  ∀ W : Submodule k (Fin n → k), ρ.IsInvariant W → W = ⊥ ∨ W = ⊤

end GaloisRep

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Mod-p Galois Representations
-- ═══════════════════════════════════════════════════════════════════════════

/-- A mod-p Galois representation: a 2-dimensional representation over 𝔽ₚ.
This is the residual representation ρ̄_{E,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ)
obtained from the p-torsion E[p] of an elliptic curve.

Requires p prime so that ZMod p is a field. -/
abbrev ModPGaloisRep (p : ℕ) [Fact (Nat.Prime p)] (K : Type*) [Field K] :=
  GaloisRep 2 (ZMod p) K

end Fermat
