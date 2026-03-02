/-
  Galois Representations Attached to Elliptic Curves (WP2)

  Defines the mod-p Galois representation ρ̄_{E,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ)
  attached to an elliptic curve E/ℚ via the p-torsion subgroup E[p].

  The p-torsion E[p] of an elliptic curve over ℚ is (for p prime, good
  reduction) a 2-dimensional 𝔽ₚ-vector space. The natural Galois action
  on E[p] gives a continuous homomorphism into GL₂(𝔽ₚ). The Weil pairing
  identifies the determinant of this representation with the mod-p
  cyclotomic character.

  For the Frey curve from a putative FLT counterexample, Mazur's theorem
  on rational isogenies implies the representation is irreducible for
  p ≥ 5. This irreducibility is a key input to Ribet's level-lowering
  theorem.

  Imperial FLT Blueprint: Chapter 3, §3.1-3.3.
-/

import Fermat.GaloisRep.Basic
import Fermat.Modularity.FreyCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option linter.dupNamespace false

-- DecidableEq on AlgebraicClosure ℚ needed for the EC group law
open Classical in
attribute [local instance] Classical.dec

namespace Fermat

open Modularity WeierstrassCurve

-- The trivial representation (ρ(g) = 1 for all g) provides an Inhabited
-- instance for GaloisRep, needed for opaque definitions below.
instance GaloisRep.instInhabited {n : ℕ} {k : Type*} [Field k]
    {K : Type*} [Field K] : Inhabited (GaloisRep n k K) :=
  ⟨⟨1⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The p-Torsion Module E[p]
-- ═══════════════════════════════════════════════════════════════════════════

/-- The p-torsion subgroup E[p] of an elliptic curve E/ℚ, viewed as a type.

Defined concretely as the kernel of the multiplication-by-p map on
the group of points E(Q̄) over the algebraic closure:

  E[p] = { P ∈ E(Q̄) | [p]P = 𝓞 }

The group law on E(Q̄) is the chord-tangent law, formalized via
`WeierstrassCurve.Affine.Point.instAddCommGroup` (requires `DecidableEq`
on the coefficient field, provided classically for `AlgebraicClosure ℚ`).

As an abelian group, E[p] ≅ (ℤ/pℤ)² for p prime not dividing the
discriminant. The Galois group Gal(Q̄/Q) acts on E[p] via its action
on Q̄-rational points. -/
noncomputable def torsionModule (E : WeierstrassCurve ℚ) (p : ℕ) : Type :=
  { P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point // p • P = 0 }

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The Mod-p Cyclotomic Character
-- ═══════════════════════════════════════════════════════════════════════════

/-- The mod-p cyclotomic character χ_p : Gal(Q̄/Q) →* (ℤ/pℤ)ˣ.

For σ ∈ Gal(Q̄/Q), χ_p(σ) is determined by σ(ζ_p) = ζ_p^{χ_p(σ)}
where ζ_p is a primitive p-th root of unity. This is a group
homomorphism because the Galois action respects the multiplicative
structure of roots of unity.

Constructed concretely via Mathlib's `modularCyclotomicCharacter`:
1. `AbsGaloisGroup ℚ = AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`
   acts on `AlgebraicClosure ℚ` as ring automorphisms.
2. `absGalToRingAut` forgets the algebra structure, mapping
   `AbsGaloisGroup ℚ →* RingAut (AlgebraicClosure ℚ)`.
3. `modularCyclotomicCharacter` sends ring automorphisms to `(ZMod p)ˣ`
   by their action on p-th roots of unity: σ(ζ) = ζ^{χ(σ)}.
4. The composition gives χ_p : Gal(Q̄/Q) →* (ZMod p)ˣ.

The key proof obligation is that `AlgebraicClosure ℚ` has exactly `p`
p-th roots of unity, which follows from `IsAlgClosed.exists_root`
applied to the cyclotomic polynomial (algebraically closed + char 0
gives a primitive p-th root). -/
private lemma card_rootsOfUnity_algClosure
    (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Fintype.card (rootsOfUnity p (AlgebraicClosure ℚ)) = p := by
  haveI : NeZero (p : AlgebraicClosure ℚ) :=
    ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_root
      (Polynomial.cyclotomic p (AlgebraicClosure ℚ))
      (Polynomial.degree_cyclotomic_pos p
        (AlgebraicClosure ℚ) hp.out.pos).ne.symm
  exact (Polynomial.isRoot_cyclotomic_iff.mp hz).card_rootsOfUnity

/-- The natural group homomorphism from the absolute Galois group
(K-algebra automorphisms of the algebraic closure) to ring
automorphisms, forgetting the algebra structure. This bridges
`Field.absoluteGaloisGroup` (a `def` opaque to typeclass search)
and Mathlib's `modularCyclotomicCharacter` (which acts on
`L ≃+* L`). -/
private noncomputable def absGalToRingAut :
    AbsGaloisGroup ℚ →*
      RingAut (AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

noncomputable def cyclotomicChar
    (p : ℕ) [Fact (Nat.Prime p)] :
    AbsGaloisGroup ℚ →* (ZMod p)ˣ :=
  haveI : NeZero p :=
    ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (card_rootsOfUnity_algClosure p)).comp
    absGalToRingAut

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. The Mod-p Galois Representation ρ̄_{E,p}
-- ═══════════════════════════════════════════════════════════════════════════

/-- The mod-p Galois representation attached to an elliptic curve E/ℚ:
  ρ̄_{E,p} : Gal(Q̄/Q) → GL₂(𝔽ₚ)

This is the representation on the p-torsion E[p] ≅ (𝔽ₚ)² after
choosing a basis. The isomorphism class (conjugacy class in GL₂)
is independent of the basis choice.

Opaque because its construction requires:
1. The group law on E (chord-tangent or Riemann-Roch)
2. The identification E[p] ≅ (𝔽ₚ)² (structure theorem for finite
   abelian groups applied to the p-torsion)
3. Continuity of the Galois action (compatibility with the profinite
   topology on Gal(Q̄/Q)) -/
opaque galRepOfCurve
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [Fact (Nat.Prime p)] :
    ModPGaloisRep p ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Structural Axioms
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (p-torsion is finite).** For p prime, p ≥ 5, and E with
nonzero discriminant, the p-torsion subgroup E[p] is a finite type.

The proof path (not yet formalized): the p-division polynomial ψ_p
has degree (p²−1)/2 (`WeierstrassCurve.natDegree_preΨ` in Mathlib),
so E[p] \ {𝓞} consists of at most p²−1 affine points. The missing
link is connecting division polynomial roots to torsion points via
the group law. -/
axiom torsionModule_fintype
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    Fintype (torsionModule E p)

/-- **Axiom (p-torsion has order p²).** Over an algebraically closed
field of characteristic 0, the p-division polynomial ψ_p is separable
of degree (p²−1)/2 in x. Each x-value gives 2 y-values, yielding
p²−1 affine torsion points plus 𝓞, so |E[p]| = p². -/
axiom torsionModule_card
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    @Fintype.card (torsionModule E p)
      (torsionModule_fintype E p hp5 hΔ) = p ^ 2

/-- **Theorem (Torsion structure).** E[p] ≅ (𝔽ₚ)² as sets.

Previously an axiom; now proved from `torsionModule_fintype` and
`torsionModule_card` via a cardinality argument:
  |E[p]| = p² = |ZMod p|² = |Fin 2 → ZMod p|. -/
theorem torsion_dim
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [hp : Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    Nonempty (torsionModule E p ≃ (Fin 2 → ZMod p)) := by
  letI : Fintype (torsionModule E p) := torsionModule_fintype E p hp5 hΔ
  haveI : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩
  refine ⟨Fintype.equivOfCardEq ?_⟩
  have h1 := torsionModule_card E p hp5 hΔ
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card p]
  convert h1

/-- **Axiom (Weil pairing).** The determinant of ρ̄_{E,p} equals
the mod-p cyclotomic character:
  det ∘ ρ̄_{E,p} = χ_p : Gal(Q̄/Q) →* (𝔽ₚ)ˣ

This follows from the Weil pairing e_p : E[p] × E[p] → μ_p, which
is a perfect, alternating, Galois-equivariant bilinear form on E[p].
The alternating property forces the determinant to land in μ_p, and
Galois equivariance identifies it with the cyclotomic character.

Imperial FLT Blueprint: Chapter 3, §3.2. -/
axiom galRep_det
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    GaloisRep.det (galRepOfCurve E p) = cyclotomicChar p

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Irreducibility of the Frey Representation (Mazur)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Mazur, 1978).** For the Frey curve attached to a putative
FLT counterexample a^p + b^p = c^p with p ≥ 5, the mod-p Galois
representation ρ̄_{E,p} is irreducible.

Proof outline (not formalized):
1. If ρ̄_{E,p} is reducible, then E has a rational p-isogeny.
2. By Mazur's theorem on rational isogenies (Eisenstein ideal paper,
   1978), the only primes p for which a semistable elliptic curve
   over ℚ can have a rational p-isogeny are p ∈ {2, 3, 5, 7}.
3. For p ≥ 11, this immediately gives irreducibility.
4. For p = 5, 7: the Frey curve has specific properties (its mod-p
   representation has large image) that rule out a rational
   p-isogeny.

This is one of the deepest inputs to the FLT proof. Mazur's theorem
is a major result in arithmetic geometry, relying on the geometry of
modular curves X₀(p).

Imperial FLT Blueprint: Chapter 3, §3.3. -/
axiom galRep_irreducible_frey
    (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    GaloisRep.IsIrreducible
      (galRepOfCurve (freyCurve a b p) p)

end Fermat
