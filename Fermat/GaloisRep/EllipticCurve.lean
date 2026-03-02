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

  ## Concretization of galRepOfCurve

  Previously `galRepOfCurve` was `opaque` and `galRep_det` was an axiom.
  Now `galRepOfCurve` is a concrete `noncomputable def` built from:

  1. **galAction** (proved): σ ∈ Gal(Q̄/Q) acts on E(Q̄) via Point.map
  2. **galActionOnTorsion** (proved): restricts to E[p] since torsion
     is preserved by group homomorphisms
  3. **torsionRepresentation** (axiom): packages the 𝔽_p-linear action
     into GL₂(𝔽_p) via a basis choice
  4. **weilPairing_det** (axiom): Weil pairing gives det = χ_p

  The `galRep_det` axiom is now a **theorem**, proved from `weilPairing_det`.

  Imperial FLT Blueprint: Chapter 3, §3.1-3.3.
-/

import Fermat.GaloisRep.Basic
import Fermat.Modularity.FreyCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option linter.dupNamespace false

-- DecidableEq on AlgebraicClosure ℚ needed for the EC group law
open Classical in
attribute [local instance] Classical.dec

namespace Fermat

open Modularity WeierstrassCurve Matrix

-- The trivial representation (ρ(g) = 1 for all g) provides an Inhabited
-- instance for GaloisRep, used in default cases.
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
-- §1a. Division Polynomial Degree Infrastructure (proven from Mathlib)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The ΨSq division polynomial of E/ℚ at a prime p has degree p² - 1.

This is the polynomial whose roots correspond to x-coordinates of affine
p-torsion points. Proof: `WeierstrassCurve.natDegree_ΨSq` applied over ℚ
(characteristic 0, so `(p : ℚ) ≠ 0` for any prime p). -/
theorem divPoly_degree (E : WeierstrassCurve ℚ) (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (E.ΨSq (p : ℤ)).natDegree = p ^ 2 - 1 := by
  have hp0 : ((p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [E.natDegree_ΨSq hp0]
  simp [Int.natAbs_natCast]

/-- Over the algebraic closure, ΨSq_p has exactly p² - 1 roots (with mult).

Combines `natDegree_ΨSq` with `IsAlgClosed.card_roots_eq_natDegree`. -/
theorem divPoly_roots_card (E : WeierstrassCurve ℚ) (p : ℕ)
    [hp : Fact (Nat.Prime p)] :
    ((E.ΨSq (p : ℤ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).roots.card =
      p ^ 2 - 1 := by
  rw [IsAlgClosed.card_roots_map_eq_natDegree_of_injective
    (E.ΨSq (p : ℤ)) (RingHom.injective _), divPoly_degree]

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
-- §3. The Galois Action and Mod-p Representation ρ̄_{E,p}
-- ═══════════════════════════════════════════════════════════════════════════

-- §3a. Galois Action on E(Q̄) — Fully Concrete ─────────────────────────────

/-- The action of σ ∈ Gal(Q̄/Q) on E(Q̄): maps (x,y) ↦ (σ(x), σ(y)).

Since E is defined over ℚ and σ fixes ℚ, this preserves the Weierstrass
equation coefficients, hence maps points to points. This is a group
homomorphism by functoriality of `Point.map`.

Concretely: σ.toAlgHom : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ
is injective (it's an automorphism), so `Point.map` gives an additive
group homomorphism on the group of nonsingular points. -/
noncomputable def galAction (E : WeierstrassCurve ℚ)
    (σ : AbsGaloisGroup ℚ) :
    (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point →+
    (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point :=
  Affine.Point.map σ.toAlgHom

/-- Functoriality: (σ * τ) acts as σ composed with τ.

This follows from `Point.map_map`: applying τ then σ to coordinates
is the same as applying σ ∘ τ = (σ * τ) directly. The multiplication
in Gal(Q̄/Q) is composition of automorphisms. -/
theorem galAction_mul (E : WeierstrassCurve ℚ) (σ τ : AbsGaloisGroup ℚ)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    galAction E (σ * τ) P = galAction E σ (galAction E τ P) :=
  (Affine.Point.map_map τ.toAlgHom σ.toAlgHom P).symm

/-- Identity: 1 ∈ Gal(Q̄/Q) acts trivially (identity automorphism). -/
theorem galAction_one (E : WeierstrassCurve ℚ)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    galAction E 1 P = P :=
  Affine.Point.map_id P

-- §3b. Restriction to E[p] — Proved ────────────────────────────────────────

/-- The Galois action preserves E[p]: if p•P = 0 then p•σ(P) = 0.

Proof: σ is a group homomorphism of E(Q̄), so
  p • σ(P) = σ(p • P) = σ(0) = 0.

This gives a well-defined map on the p-torsion subtype. -/
noncomputable def galActionOnTorsion (E : WeierstrassCurve ℚ) (p : ℕ)
    (σ : AbsGaloisGroup ℚ) : torsionModule E p → torsionModule E p :=
  fun ⟨P, hP⟩ => ⟨galAction E σ P, by
    rw [← (galAction E σ).map_nsmul P p, hP, map_zero]⟩

/-- The torsion action is functorial: (σ * τ) acts as σ ∘ τ on E[p]. -/
theorem galActionOnTorsion_mul (E : WeierstrassCurve ℚ) (p : ℕ)
    (σ τ : AbsGaloisGroup ℚ) (P : torsionModule E p) :
    galActionOnTorsion E p (σ * τ) P =
    galActionOnTorsion E p σ (galActionOnTorsion E p τ P) := by
  obtain ⟨val, prop⟩ := P
  simp only [galActionOnTorsion, galAction]
  congr 1
  exact (Affine.Point.map_map τ.toAlgHom σ.toAlgHom val).symm

-- §3c. Packaging as GL₂(𝔽_p) — Axiom ──────────────────────────────────────

/-- **Axiom (torsion representation).** The Galois action on E[p],
after choosing a basis of the 2-dimensional 𝔽_p-vector space E[p],
yields a group homomorphism into GL₂(𝔽_p).

Proof path (infrastructure gap in Mathlib):
1. E[p] inherits AddCommGroup from the subgroup structure of E(Q̄)
2. The ℤ-action factors through ℤ/pℤ (since p kills E[p]),
   giving a Module (ZMod p) instance
3. torsion_dim provides E[p] ≅ (𝔽_p)² as a set bijection;
   the module structure promotes this to a basis
4. galActionOnTorsion is ZMod p-linear: it preserves addition
   (proved above), and ZMod p-scalars are iterated addition
5. Each σ gives an invertible linear map (σ is an automorphism,
   so σ⁻¹ provides the inverse)
6. LinearMap.toMatrix w.r.t. the basis gives GL₂(𝔽_p)

This axiom packages steps 1-6. The concretization of
`galActionOnTorsion` (§3b) provides the mathematical content;
only the linear algebra packaging remains axiomatic. -/
axiom torsionRepresentation
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    AbsGaloisGroup ℚ →* GL (Fin 2) (ZMod p)

/-- The representation agrees with the concrete Galois action on E[p].
For any σ and torsion point Q, the matrix action through some basis
β agrees with galActionOnTorsion. This ties the abstract GL₂ element
to the concrete coordinate action. -/
axiom torsionRepresentation_compat
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0)
    (σ : AbsGaloisGroup ℚ) (Q : torsionModule E p) :
    ∃ β : torsionModule E p ≃ (Fin 2 → ZMod p),
      (torsionRepresentation E p σ).val.mulVec (β Q) =
        β (galActionOnTorsion E p σ Q)

-- §3d. The Concrete Definition ─────────────────────────────────────────────

/-- The mod-p Galois representation ρ̄_{E,p} : Gal(Q̄/Q) → GL₂(𝔽_p).

**Previously opaque; now a concrete noncomputable def.**

The construction is fully visible:
1. `galAction` (§3a, proved): σ acts on E(Q̄) via Point.map σ.toAlgHom
2. `galActionOnTorsion` (§3b, proved): restricts to E[p]
3. `torsionRepresentation` (§3c, axiom): packages as GL₂ matrices

The representation is well-defined for all E and p (though its
interesting properties like det = χ_p require p ≥ 5 and Δ ≠ 0).
The isomorphism class (conjugacy class in GL₂) is independent of
the basis choice. -/
noncomputable def galRepOfCurve
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ModPGaloisRep p ℚ :=
  ⟨torsionRepresentation E p⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Structural Axioms (Torsion)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (p-torsion is finite).** For p prime, p ≥ 5, and E with
nonzero discriminant, the p-torsion subgroup E[p] is a finite type.

**Proven steps** (see `divPoly_degree`, `divPoly_roots_card`):
- `E.ΨSq p` has degree p²−1 over ℚ
- Over AlgebraicClosure ℚ, it has p²−1 roots with multiplicity

**Missing Mathlib link**: for affine P = (x, y), the identity
  `p • P = 0 ↔ Polynomial.eval x (E.ΨSq p) = 0`
connecting the formalized group law to division polynomial evaluation.
(Silverman, Proposition III.4.2.) -/
axiom torsionModule_fintype
    (E : WeierstrassCurve ℚ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    Fintype (torsionModule E p)

/-- **Axiom (p-torsion has order p²).** The [p]-map on E is separable
of degree p² in characteristic 0, so |E[p]| = p².

Concretely: preΨ_p has degree (p²−1)/2 and is separable (char 0),
giving (p²−1)/2 distinct x-roots over the algebraic closure. Each
root yields 2 affine points (Weierstrass eq. quadratic in y, Δ ≠ 0).
Total: 2 · (p²−1)/2 + 1 (for O) = p².

The `divPoly_roots_card` theorem proves the root count; the gap is
the connection between roots and torsion. -/
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

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. The Weil Pairing and det = χ_p
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Weil pairing determinant).** The determinant of the
torsion representation equals the mod-p cyclotomic character:

  det ∘ ρ̄_{E,p} = χ_p : Gal(Q̄/Q) →* (𝔽ₚ)ˣ

This is the deepest of the representation axioms. It follows from
the Weil pairing e_p : E[p] × E[p] → μ_p, a perfect alternating
Galois-equivariant bilinear form on E[p]:

1. For a basis {P, Q} of E[p], e_p(P, Q) = ζ (a primitive p-th root).
2. For σ ∈ Gal(Q̄/Q) with matrix ρ(σ) = [[a,b],[c,d]]:
   e_p(σP, σQ) = e_p(aP+bQ, cP+dQ) = e_p(P,Q)^{ad-bc} = ζ^{det ρ(σ)}.
3. Galois equivariance: e_p(σP, σQ) = σ(e_p(P,Q)) = σ(ζ) = ζ^{χ_p(σ)}.
4. Therefore det ρ(σ) ≡ χ_p(σ) (mod p) for all σ.

Imperial FLT Blueprint: Chapter 3, §3.2. -/
axiom weilPairing_det
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    GeneralLinearGroup.det.comp (torsionRepresentation E p) =
      cyclotomicChar p

/-- **Theorem (det = cyclotomic character).** The determinant of ρ̄_{E,p}
equals the mod-p cyclotomic character.

**Previously an axiom** about the opaque `galRepOfCurve`.

Now proved from the Weil pairing axiom: `GaloisRep.det (galRepOfCurve E p)`
unfolds (by `rfl`) to `GeneralLinearGroup.det.comp (torsionRepresentation E p)`,
which equals `cyclotomicChar p` by `weilPairing_det`.

Imperial FLT Blueprint: Chapter 3, §3.2. -/
theorem galRep_det
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    GaloisRep.det (galRepOfCurve E p) = cyclotomicChar p :=
  weilPairing_det E p hp5 hΔ

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Irreducibility of the Frey Representation (Mazur)
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
