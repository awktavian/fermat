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

  Imperial FLT Blueprint: Chapter 3, §3.1–3.3.
-/

import Fermat.GaloisRep.Basic
import Fermat.Modularity.FreyCurve

set_option linter.dupNamespace false

namespace Fermat

open Modularity

-- The trivial representation (ρ(g) = 1 for all g) provides an Inhabited
-- instance for GaloisRep, needed for opaque definitions below.
instance GaloisRep.instInhabited {n : ℕ} {k : Type*} [Field k]
    {K : Type*} [Field K] : Inhabited (GaloisRep n k K) :=
  ⟨⟨1⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The p-Torsion Module E[p]
-- ═══════════════════════════════════════════════════════════════════════════

/-- The p-torsion subgroup E[p] of an elliptic curve E/ℚ, viewed as
a type. As an abelian group, E[p] ≅ (ℤ/pℤ)² for p prime not dividing
the discriminant (good ordinary or supersingular reduction). The Galois
group Gal(Q̄/Q) acts on E[p] by its action on Q̄-rational points.

This is opaque because constructing E[p] requires the group law on
the elliptic curve, which depends on the Riemann-Roch theorem for
curves (or an explicit Weierstrass chord-tangent construction). -/
opaque torsionModule (E : WeierstrassCurve ℚ) (p : ℕ) : Type

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The Mod-p Cyclotomic Character
-- ═══════════════════════════════════════════════════════════════════════════

/-- The mod-p cyclotomic character χ_p : Gal(Q̄/Q) →* (ℤ/pℤ)ˣ.

For σ ∈ Gal(Q̄/Q), χ_p(σ) is determined by σ(ζ_p) = ζ_p^{χ_p(σ)}
where ζ_p is a primitive p-th root of unity. This is a group
homomorphism because the Galois action respects the multiplicative
structure of roots of unity.

Opaque because constructing it requires the p-th cyclotomic extension
and its Galois theory (available in mathlib's cyclotomic library, but
the connection to the absolute Galois group requires nontrivial
functoriality). -/
opaque cyclotomicChar (p : ℕ) [Fact (Nat.Prime p)] :
    AbsGaloisGroup ℚ →* (ZMod p)ˣ

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
opaque galRepOfCurve (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ModPGaloisRep p ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Structural Axioms
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Torsion structure theorem).** For p prime, p ≥ 5, and E
with nonzero discriminant (hence non-singular), the p-torsion E[p]
is isomorphic to (𝔽ₚ)² as a set — equivalently, as an 𝔽ₚ-vector
space it has dimension 2.

This is a theorem of algebraic geometry: for an elliptic curve over
an algebraically closed field of characteristic 0 (or characteristic
not equal to p), the p-torsion is isomorphic to (ℤ/pℤ)².

The hypothesis p ≥ 5 is stronger than necessary (p ≥ 2 suffices for
the structure theorem) but matches our FLT application. The hypothesis
Δ ≠ 0 ensures E is non-singular. -/
axiom torsion_dim (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5) (hΔ : E.Δ ≠ 0) :
    Nonempty (torsionModule E p ≃ Fin 2 → ZMod p)

/-- **Axiom (Weil pairing).** The determinant of ρ̄_{E,p} equals the
mod-p cyclotomic character:
  det ∘ ρ̄_{E,p} = χ_p : Gal(Q̄/Q) →* (𝔽ₚ)ˣ

This follows from the Weil pairing e_p : E[p] × E[p] → μ_p, which
is a perfect, alternating, Galois-equivariant bilinear form on E[p].
The alternating property forces the determinant to land in μ_p, and
Galois equivariance identifies it with the cyclotomic character.

Imperial FLT Blueprint: Chapter 3, §3.2. -/
axiom galRep_det (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
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
   representation has large image) that rule out a rational p-isogeny.

This is one of the deepest inputs to the FLT proof. Mazur's theorem
is a major result in arithmetic geometry, relying on the geometry of
modular curves X₀(p).

Imperial FLT Blueprint: Chapter 3, §3.3 (p-torsion reducibility). -/
axiom galRep_irreducible_frey (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    GaloisRep.IsIrreducible (galRepOfCurve (freyCurve a b p) p)

end Fermat
