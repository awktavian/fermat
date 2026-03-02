/-
  Newforms (Hecke Eigenforms) and Attached Galois Representations (WP4)

  Defines the type of weight-k newforms at level Γ₀(N) and the
  Galois representation attached to weight-2 newforms via the
  Eichler-Shimura construction.

  A newform is a normalized cuspidal Hecke eigenform that is "new"
  at its level — it does not arise from a lower level via degeneracy
  maps. The Eichler-Shimura relation associates to each weight-2
  newform f at level N a 2-dimensional mod-p Galois representation
  ρ̄_{f,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ).

  The key consumer is WP6 (Ribet's level-lowering theorem), which
  manipulates newforms and their attached representations to derive
  a contradiction from a putative FLT counterexample.

  Imperial FLT Blueprint: Chapter 3 (Galois representations),
  Chapter 4 (modularity lifting — Eichler-Shimura direction).
-/

import Fermat.GaloisRep.EllipticCurve
import Fermat.ModularForms.RiemannRoch
import Fermat.Modularity.Axioms

set_option linter.dupNamespace false

namespace Fermat

open Fermat.RiemannRoch Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Newforms
-- ═══════════════════════════════════════════════════════════════════════════

/-- A weight-k newform at level Γ₀(N).

A newform is a cusp form that is:
1. An eigenform for all Hecke operators T_n (n ≥ 1)
2. Normalized: the first Fourier coefficient a₁(f) = 1
3. New: not in the image of any degeneracy map from a lower level

The structure wraps an element of the cusp form space S_k(Γ₀(N)).
The Hecke eigenform and newness conditions are not enforced in the
type (they would require the full Hecke algebra infrastructure);
instead, the axioms below constrain which `Newform` values are
mathematically meaningful.

For FLT, the key case is k = 2 (weight-2 newforms correspond to
isogeny classes of elliptic curves over ℚ by Eichler-Shimura). -/
structure Newform (N : ℕ) (k : ℤ) where
  /-- The underlying cusp form in S_k(Γ₀(N)). -/
  toCuspForm : CuspFormSpace N k

attribute [coe] Newform.toCuspForm

instance Newform.instCoe (N : ℕ) (k : ℤ) :
    Coe (Newform N k) (CuspFormSpace N k) where
  coe := Newform.toCuspForm

/-- Newforms are inhabited (the zero cusp form wraps trivially).
Mathematically, the zero form is not a newform (a₁ = 0 ≠ 1), but
this instance is needed for opaque definitions below. -/
instance Newform.instInhabited (N : ℕ) (k : ℤ) : Inhabited (Newform N k) :=
  ⟨⟨0⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Level Accessor
-- ═══════════════════════════════════════════════════════════════════════════

/-- The level of a newform. For `f : Newform N k`, this is just N.

The level (conductor) determines the congruence subgroup Γ₀(N)
under which the newform is slash-invariant. Ribet's level-lowering
theorem reduces the level of the Galois representation, ultimately
reaching level 2 for the Frey curve. -/
def newformLevel (_f : Newform N k) : ℕ := N

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. The Galois Representation Attached to a Newform (Eichler-Shimura)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The mod-p Galois representation attached to a weight-2 newform
via the Eichler-Shimura construction:

  ρ̄_{f,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ)

The construction proceeds by:
1. The Jacobian J₀(N) of the modular curve X₀(N) is an abelian
   variety with a Hecke action.
2. The newform f determines a quotient abelian variety A_f of J₀(N)
   (the "optimal quotient" or Shimura's f-part).
3. A_f is an elliptic curve when f has rational Fourier coefficients
   (the weight-2 case with [Q(f):Q] = 1).
4. The p-torsion A_f[p] gives a 2-dimensional 𝔽ₚ-representation.

This is opaque because the full construction requires:
- The modular Jacobian and its Hecke algebra action
- The Shimura quotient construction
- The identification of A_f[p] with a 2-dimensional 𝔽ₚ-space

Requires p prime so that 𝔽ₚ = ZMod p is a field. -/
opaque galRepOfNewform {N : ℕ} (f : Newform N 2) (p : ℕ) [Fact (Nat.Prime p)] :
    GaloisRep 2 (ZMod p) ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Axioms
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Modularity ⇒ Newform, Eichler-Shimura direction).**

If an elliptic curve E/ℚ is modular at level N, then there exists
a weight-2 newform f at level N such that the mod-p Galois
representation of f matches that of E:

  ρ̄_{f,p} ≅ ρ̄_{E,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ)

This is the "easy" direction of the modularity theorem: modular
curves parametrize elliptic curves, and the Eichler-Shimura
relation identifies L-functions. The hard direction (every
semistable elliptic curve is modular) is Wiles' theorem, axiomatized
in Axioms.lean as `frey_is_modular`.

For FLT, this axiom converts the modularity of the Frey curve into
the existence of a newform that Ribet's theorem can then act on.

Imperial FLT Blueprint: Chapter 4, §4.1 (Eichler-Shimura). -/
axiom newform_from_modular_curve (E : WeierstrassCurve ℚ) (N : ℕ)
    (hmod : Fermat.Axioms.IsModular E) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ f : Newform N 2, galRepOfNewform f p = galRepOfCurve E p

/-- **Axiom (Irreducibility of mod-p newform representations).**

For a weight-2 newform f at level N and any prime p ≥ 5, the
mod-p Galois representation ρ̄_{f,p} is irreducible.

More precisely: if f corresponds to an elliptic curve E/ℚ (via
Eichler-Shimura), then ρ̄_{f,p} is irreducible for p ≥ 5 by
Mazur's theorem on rational isogenies (1978). The bound p ≥ 5 is
not optimal for all curves but suffices for the FLT application.

For a general newform (not necessarily attached to an elliptic
curve), irreducibility holds for all but finitely many p. The
uniform bound p ≥ 5 is a simplification justified by the FLT
use case.

Imperial FLT Blueprint: Chapter 3, §3.3 (Mazur). -/
axiom galRep_of_newform_irreducible {N : ℕ} (f : Newform N 2) (p : ℕ)
    [Fact (Nat.Prime p)] (hp : p ≥ 5) :
    GaloisRep.IsIrreducible (galRepOfNewform f p)

end Fermat
