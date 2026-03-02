/-
  Classification of Hardly Ramified Mod 3 Galois Representations

  Theorem 3.9 (Buzzard–Taylor, Imperial FLT Blueprint):
  If L/ℚ₃ is a finite extension with integer ring O_L, and
  ρ₃ : Gal(Q̄/Q) → GL₂(O_L) is hardly ramified, then (viewed as a
  representation to GL₂(L)) the semisimplification satisfies
    ρ₃^{ss} ≅ 1 ⊕ χ₃
  where 1 is the trivial character and χ₃ is the 3-adic cyclotomic character.

  The proof combines:
  1. Fontaine's theorem: no nontrivial abelian scheme over Spec(ℤ)
  2. Odlyzko discriminant bounds: prevent certain number fields from existing
  3. Fontaine–Laffaille theory: hardly ramified reps ↔ finite flat group schemes

  These are axiomatized. The value of this file is the TYPE ARCHITECTURE:
  connecting the hardly ramified condition, semisimplification, direct sum
  decomposition, and cyclotomic characters to the rest of the proof.

  Note on coefficients: The blueprint works over O_L (an integer ring) and L
  (a field). Since `GaloisRep n k K` requires `Field k`, we formalize
  everything over a field L. The integral structure is absorbed into the
  `IsHardlyRamified3adic` predicate.

  Imperial FLT Blueprint: Chapter 3, §3.9.
-/

import Fermat.GaloisRep.Basic

set_option linter.dupNamespace false

namespace Fermat

-- Inhabited instance for GaloisRep (trivial representation ρ(g) = 1).
-- Needed by opaque definitions below.
instance GaloisRep.instInhabitedAux {n : ℕ} {k : Type*} [Field k]
    {K : Type*} [Field K] : Inhabited (GaloisRep n k K) :=
  ⟨⟨1⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Hardly Ramified at ℓ = 3
-- ═══════════════════════════════════════════════════════════════════════════

/-- A 2-dimensional Galois representation ρ : Gal(Q̄/Q) → GL₂(L) is
**hardly ramified at 3** if, informally, the restriction to the inertia
group I₃ ⊂ Gal(Q̄₃/Q₃) has very constrained image — specifically, ρ|_{I₃}
factors through a finite flat group scheme over ℤ₃ that extends to ℤ.

More precisely (Fontaine–Laffaille): ρ is hardly ramified at ℓ if ρ|_{G_ℓ}
arises from a finite flat group scheme over O_K where K is unramified over
ℚ_ℓ. For ℓ = 3, this is the condition that appears in Wiles's modularity
lifting theorem (the "flat at 3" hypothesis).

This specialization to ℓ = 3 is the case relevant to FLT: the mod-3
representation of the Frey curve is hardly ramified when 3 ∤ abc.

Opaque because the definition requires:
1. The decomposition/inertia group at 3 in Gal(Q̄/Q)
2. Fontaine–Laffaille theory (crystalline representations ↔ filtered modules)
3. The flat group scheme classification over ℤ₃

Imperial FLT Blueprint: Chapter 3, Definition 3.8. -/
opaque IsHardlyRamified3adic {L : Type*} [Field L]
    (ρ : GaloisRep 2 L ℚ) : Prop

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Semisimplification
-- ═══════════════════════════════════════════════════════════════════════════

/-- The semisimplification ρ^{ss} of a 2-dimensional Galois representation.

For a 2-dimensional representation ρ : Gal(Q̄/Q) → GL₂(L):
- If ρ is irreducible, ρ^{ss} = ρ.
- If ρ is reducible (has a 1-dimensional invariant subspace), then
  ρ^{ss} = χ₁ ⊕ χ₂ where χ₁, χ₂ are the Jordan–Hölder factors.
  Concretely, ρ is conjugate to an upper triangular representation
  (χ₁  *; 0  χ₂) and ρ^{ss} = (χ₁  0; 0  χ₂).

The semisimplification is well-defined up to isomorphism (by the
Jordan–Hölder theorem for representations).

Opaque because it requires:
1. Existence of invariant subspaces (or proof of irreducibility)
2. The Jordan–Hölder theorem for finite-dimensional representations
3. Choosing a complement (or canonical diagonal form) -/
opaque semisimplification {L : Type*} [Field L]
    (ρ : GaloisRep 2 L ℚ) : GaloisRep 2 L ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Direct Sum of Characters
-- ═══════════════════════════════════════════════════════════════════════════

/-- The direct sum χ₁ ⊕ χ₂ of two 1-dimensional Galois representations
(characters), viewed as a 2-dimensional representation.

Given χ₁, χ₂ : Gal(Q̄/Q) →* GL₁(L) ≅ Lˣ, the direct sum is:
  (χ₁ ⊕ χ₂)(g) = diag(χ₁(g), χ₂(g)) ∈ GL₂(L)

This is the diagonal block embedding GL₁ × GL₁ ↪ GL₂.

Opaque because the identification GL₁(L) ≅ Lˣ and the diagonal
embedding into GL₂(L) require matrix algebra bookkeeping that is
straightforward but verbose. -/
opaque directSumChar {L : Type*} [Field L]
    (χ₁ χ₂ : GaloisRep 1 L ℚ) : GaloisRep 2 L ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. The Trivial Character
-- ═══════════════════════════════════════════════════════════════════════════

/-- The trivial character 1 : Gal(Q̄/Q) →* GL₁(L), sending every element
of the Galois group to the identity matrix.

As a 1-dimensional representation over L, this is the representation on
a 1-dimensional L-vector space where Galois acts trivially:
  1(g) = (1) ∈ GL₁(L) for all g ∈ Gal(Q̄/Q).

Note: The blueprint defines this over the integer ring O_L, but since
`GaloisRep` requires a `Field` coefficient, we define it over L. The
integrality is implicit — the trivial character has image in GL₁(O_L)
since the identity matrix has integral entries. -/
opaque trivialChar (L : Type*) [Field L] : GaloisRep 1 L ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. The 3-adic Cyclotomic Character
-- ═══════════════════════════════════════════════════════════════════════════

/-- The 3-adic cyclotomic character χ₃ : Gal(Q̄/Q) →* GL₁(L).

For σ ∈ Gal(Q̄/Q), the 3-adic cyclotomic character is determined by:
  σ(ζ_{3^n}) = ζ_{3^n}^{χ₃(σ)} for all n ≥ 1
where ζ_{3^n} is a primitive 3^n-th root of unity. Taking the inverse
limit gives χ₃ : Gal(Q̄/Q) → ℤ₃ˣ ↪ Lˣ ≅ GL₁(L), where the embedding
ℤ₃ˣ ↪ Lˣ uses the structural map ℤ₃ → O_L → L.

This is the ℓ-adic cyclotomic character specialized to ℓ = 3. It factors
through Gal(ℚ(μ_{3^∞})/ℚ) ≅ ℤ₃ˣ. The mod-3 reduction recovers the
mod-3 cyclotomic character `cyclotomicChar 3` from EllipticCurve.lean.

Note: As with `trivialChar`, the blueprint defines this over O_L but we
formalize over L. The image lies in GL₁(O_L) since χ₃ takes values in ℤ₃ˣ. -/
opaque cyclotomic3Char (L : Type*) [Field L] : GaloisRep 1 L ℚ

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Abelian Schemes over Spec(ℤ) (Supporting Types)
-- ═══════════════════════════════════════════════════════════════════════════

/-- An abelian scheme over Spec(ℤ). This is an abelian variety defined
over the integers — equivalently, a smooth proper group scheme over ℤ
with connected geometric fibers.

Examples: the trivial abelian scheme (dimension 0) is the only one,
by Fontaine's theorem (§7).

Opaque because the full definition requires:
1. The theory of group schemes over ℤ (not in mathlib)
2. Smoothness and properness over Spec(ℤ)
3. Connectedness of geometric fibers -/
opaque AbelianSchemeOverZ : Type

/-- The dimension of an abelian scheme A/Spec(ℤ). For A an abelian variety,
dim(A) is the dimension of the underlying algebraic variety. The trivial
scheme has dimension 0. -/
opaque AbelianSchemeOverZ.dimension : AbelianSchemeOverZ → ℕ

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Fontaine's Theorem (No Nontrivial Abelian Schemes over ℤ)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Fontaine, 1985).** Every abelian scheme over Spec(ℤ) is trivial
(has dimension 0).

Equivalently: there is no abelian variety of positive dimension with
everywhere good reduction over ℚ. This is because an abelian variety
A/ℚ with everywhere good reduction would extend to a smooth proper group
scheme over ℤ, and the associated ℓ-adic Galois representation would be
unramified everywhere — but such representations don't exist for geometric
reasons (the associated number fields would violate Odlyzko discriminant
bounds, see §8).

In the FLT context: Fontaine's theorem implies that certain finite flat
group schemes over ℤ₃ that arise from hardly ramified representations
cannot have "interesting" structure, forcing the semisimplification to
decompose as 1 ⊕ χ₃.

Proof (sketch, not formalized):
1. If A/ℤ has dim ≥ 1, then A[ℓ] gives a nontrivial finite flat group
   scheme over ℤ, hence an unramified-everywhere Galois representation.
2. The associated number field K has discriminant 1 (unramified everywhere).
3. By Minkowski/Odlyzko (§8), K = ℚ — contradiction with nontriviality.

Reference: Fontaine, "Il n'y a pas de variété abélienne sur ℤ" (1985). -/
axiom fontaine_no_abelian_scheme_over_Z :
    ∀ (A : AbelianSchemeOverZ), A.dimension = 0

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Odlyzko Discriminant Bound
-- ═══════════════════════════════════════════════════════════════════════════

/-- A number field K/ℚ, viewed as a type. This is a finite extension of ℚ.
Opaque because the full infrastructure (ring of integers, discriminant,
ramification) is not needed here — we only need the discriminant bound. -/
opaque NumberField : Type

/-- The degree [K : ℚ] of a number field. -/
opaque NumberField.degree : NumberField → ℕ

/-- The absolute discriminant disc(K/ℚ) of a number field, as a natural
number (we take the absolute value since only the magnitude matters
for the Odlyzko bound). -/
opaque NumberField.absDiscriminant : NumberField → ℕ

/-- A number field is unramified everywhere (at all finite primes) if its
discriminant equals 1 (equivalently, all primes are unramified in K/ℚ).
This is the condition that arises from abelian schemes over ℤ via their
associated Galois representations. -/
opaque NumberField.isEverywhereUnramified : NumberField → Prop

/-- **Axiom (Odlyzko, 1976; Minkowski for the base case).** There is no
nontrivial number field that is unramified at every prime.

Equivalently: the only number field with |disc(K)| = 1 is K = ℚ itself.
For degree [K:ℚ] ≥ 2, Odlyzko's unconditional lower bounds give
  |disc(K)|^{1/[K:ℚ]} ≥ 2π·e^γ ≈ 22.3... (under GRH)
  |disc(K)|^{1/[K:ℚ]} ≥ 60.8...          (unconditionally, as [K:ℚ] → ∞)
which in particular implies |disc(K)| > 1 for [K:ℚ] ≥ 2.

The Minkowski bound already suffices: |disc(K)| ≥ (π/4)^{r₂} · (n^n/n!) / 4^n
where n = [K:ℚ], giving |disc(K)| > 1 for n ≥ 2. Odlyzko provides much
sharper bounds needed for higher-dimensional applications.

This is the number-theoretic input to Fontaine's theorem (§7): an abelian
scheme over ℤ would produce unramified-everywhere representations, hence
unramified-everywhere number fields, which don't exist by this bound.

Reference: Odlyzko, "Discriminant bounds" (1976), Tables updated 1990. -/
axiom odlyzko_discriminant_bound :
    ∀ (K : NumberField), NumberField.isEverywhereUnramified K →
      NumberField.degree K ≤ 1

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Theorem 3.9: Classification of Hardly Ramified Mod 3 Representations
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Theorem 3.9, Buzzard–Taylor / Imperial FLT Blueprint).**
Classification of hardly ramified mod 3 Galois representations.

If ρ : Gal(Q̄/Q) → GL₂(L) is hardly ramified at 3, then its
semisimplification decomposes as:
  ρ^{ss} = 1 ⊕ χ₃
where 1 is the trivial character and χ₃ is the 3-adic cyclotomic character.

Proof outline (not formalized):
1. By Fontaine–Laffaille theory, a hardly ramified representation at 3
   corresponds to a finite flat group scheme G over ℤ₃.
2. G extends to a finite flat group scheme over ℤ (by the hardly ramified
   condition and a patching argument using Odlyzko bounds at other primes).
3. By Fontaine's theorem (§7, `fontaine_no_abelian_scheme_over_Z`), the
   associated abelian scheme is trivial, so G has constrained structure.
4. The only 2-dimensional semisimple representation with this constraint
   is 1 ⊕ χ₃ (the trivial character and the cyclotomic character arise
   from the connected-étale sequence of G).

This classification is used in Wiles's modularity lifting argument:
the mod-3 representation of an elliptic curve with good reduction at 3
is hardly ramified, and this theorem constrains its semisimplification.

Imperial FLT Blueprint: Chapter 3, Theorem 3.9. -/
axiom mod3_classification {L : Type*} [Field L]
    (ρ : GaloisRep 2 L ℚ) (hhr : IsHardlyRamified3adic ρ) :
    semisimplification ρ = directSumChar (trivialChar L) (cyclotomic3Char L)

end Fermat
