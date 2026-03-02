/-
  Ramification Infrastructure for Galois Representations (WP-RAM)

  Concretizes the inertia group at a prime ℓ for Gal(Q̄/Q) using Mathlib's
  ValuationSubring.decompositionSubgroup and ValuationSubring.inertiaSubgroup.

  The construction:
  1. The ℓ-adic valuation subring of ℚ (via HeightOneSpectrum of ℤ)
  2. A valuation subring of AlgebraicClosure ℚ extending it (Chevalley's theorem)
  3. The decomposition subgroup D_ℓ ⊂ Gal(Q̄/Q) (stabilizer of the extension)
  4. The inertia subgroup I_ℓ ◁ D_ℓ (kernel of residue field action)

  The one mathematical gap: the existence of a valuation extending the ℓ-adic
  valuation from ℚ to AlgebraicClosure ℚ (Chevalley's extension theorem,
  a standard application of Zorn's lemma). This is stated as a sorry-backed
  lemma, with a clear path to resolution once Mathlib gains the extension
  theorem for valuations along algebraic extensions.

  The definition of IsUnramifiedAt is independent of the choice of extending
  valuation: all extensions are conjugate under Gal(Q̄/Q), so the inertia
  subgroup is well-defined up to conjugacy, and "ρ trivial on I_ℓ" is
  conjugacy-invariant.

  Mathlib APIs used:
  - ValuationSubring.decompositionSubgroup (RingTheory.Valuation.RamificationGroup)
  - ValuationSubring.inertiaSubgroup (RingTheory.Valuation.RamificationGroup)
  - IsDedekindDomain.HeightOneSpectrum (RingTheory.DedekindDomain.Ideal.Lemmas)
  - HeightOneSpectrum.valuation (RingTheory.DedekindDomain.AdicValuation)
  - Rat.isFractionRing : IsFractionRing ℤ ℚ

  Imperial FLT Blueprint: Chapter 3, §3.2 (ramification at primes of the conductor).
-/

import Fermat.GaloisRep.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Data.Nat.Prime.Int

set_option linter.dupNamespace false

namespace Fermat

open IsDedekindDomain ValuationSubring

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The ℓ-adic Valuation Subring of ℚ
-- ═══════════════════════════════════════════════════════════════════════════

/-- The height-one prime of ℤ corresponding to a natural number prime ℓ.

This constructs the prime ideal ℓℤ ⊂ ℤ as an element of the height-one
spectrum of the Dedekind domain ℤ. -/
noncomputable def primeIdealOfNat (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(ℓ : ℤ)}
  isPrime := by
    rw [Ideal.span_singleton_prime (show (ℓ : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr hℓ.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hℓ
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hℓ.ne_zero

/-- The ℓ-adic valuation subring of ℚ: the subring of rational numbers with
non-negative ℓ-adic valuation, i.e., rationals whose denominator is coprime to ℓ.

This is ℤ_(ℓ), the localization of ℤ at the prime ℓ, viewed as a valuation
subring of the fraction field ℚ.

The type annotation `(ℚ := ℚ)` ensures Lean resolves ℚ as the fraction ring
of ℤ via `Rat.isFractionRing`. -/
noncomputable def adicValuationSubringQ (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    ValuationSubring ℚ :=
  ((primeIdealOfNat ℓ hℓ).valuation (K := ℚ)).valuationSubring

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Extension of Valuations to Algebraic Closure (Chevalley)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Chevalley's extension theorem** (for valuation subrings of ℚ).

For any valuation subring V of ℚ, there exists a valuation subring W of
the algebraic closure Q̄ = AlgebraicClosure ℚ such that W restricts to V,
i.e., W.comap (algebraMap ℚ Q̄) = V.

This is a standard consequence of Zorn's lemma:
1. The integral closure of V in Q̄ is a local ring
2. By `LocalSubring.exists_le_valuationSubring`, any local subring
   of a field can be dominated by a valuation subring
3. The resulting valuation subring restricts to V

Once Mathlib gains `Valuation.exists_extension_of_isAlgebraic` or equivalent,
this sorry can be eliminated. -/
lemma exists_valuationSubring_extension (V : ValuationSubring ℚ) :
    ∃ W : ValuationSubring (AlgebraicClosure ℚ),
      W.comap (algebraMap ℚ (AlgebraicClosure ℚ)) = V := by
  sorry

/-- A nonconstructive choice of valuation subring of Q̄ extending a given
valuation subring of ℚ. -/
noncomputable def valuationSubringOver (V : ValuationSubring ℚ) :
    ValuationSubring (AlgebraicClosure ℚ) :=
  (exists_valuationSubring_extension V).choose

theorem valuationSubringOver_comap (V : ValuationSubring ℚ) :
    (valuationSubringOver V).comap (algebraMap ℚ (AlgebraicClosure ℚ)) = V :=
  (exists_valuationSubring_extension V).choose_spec

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Decomposition and Inertia Subgroups
-- ═══════════════════════════════════════════════════════════════════════════

/-- The decomposition subgroup D_ℓ ⊂ Gal(Q̄/Q) at a prime ℓ.

This is the stabilizer of a chosen valuation subring W of Q̄ extending the
ℓ-adic valuation on ℚ. Different choices of W give conjugate subgroups.

Mathematically, D_ℓ is isomorphic to the local Galois group Gal(Q̄_ℓ/Q_ℓ). -/
noncomputable def decompositionGroupAt (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    Subgroup (AbsGaloisGroup ℚ) :=
  (valuationSubringOver (adicValuationSubringQ ℓ hℓ)).decompositionSubgroup ℚ

/-- The inertia subgroup I_ℓ ⊂ Gal(Q̄/Q) at a prime ℓ.

Elements of I_ℓ act trivially on the residue field of the chosen valuation
subring W of Q̄. The inertia group fits in a short exact sequence:
  1 → I_ℓ → D_ℓ → Gal(k̄/k) → 1
where k = 𝔽_ℓ is the residue field.

We map the inertia subgroup (a subgroup of D_ℓ) into Gal(Q̄/Q) via
the inclusion D_ℓ ↪ Gal(Q̄/Q). -/
noncomputable def inertiaGroupAt (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    Subgroup (AbsGaloisGroup ℚ) :=
  let W := valuationSubringOver (adicValuationSubringQ ℓ hℓ)
  Subgroup.map (W.decompositionSubgroup ℚ).subtype (W.inertiaSubgroup ℚ)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. The Unramified Predicate
-- ═══════════════════════════════════════════════════════════════════════════

/-- A mod-p Galois representation ρ : Gal(Q̄/Q) → GL₂(𝔽ₚ) is **unramified
at a prime ℓ** if every element of the inertia group I_ℓ acts trivially:
ρ(σ) = 1 for all σ ∈ I_ℓ ⊂ Gal(Q̄/Q).

Equivalently, ρ factors through Gal(Q̄/Q) / I_ℓ, so the representation is
determined by the Frobenius element at ℓ.

This definition is mathematically canonical: it depends on the choice of
extending valuation, but any two choices are conjugate under Gal(Q̄/Q), and
"ρ trivial on I_ℓ" is invariant under conjugation (ρ(σ·τ·σ⁻¹) = 1 iff ρ(τ) = 1
for group homomorphisms ρ).

If ℓ is not prime, the predicate is vacuously true (the inertia group is only
defined for primes). -/
def IsUnramifiedAt {p : ℕ} [Fact (Nat.Prime p)]
    (ρ : GaloisRep 2 (ZMod p) ℚ) (ℓ : ℕ) : Prop :=
  ∀ (hℓ : Nat.Prime ℓ), ∀ σ ∈ inertiaGroupAt ℓ hℓ, ρ.toMonoidHom σ = 1

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Basic Properties
-- ═══════════════════════════════════════════════════════════════════════════

/-- A representation is vacuously unramified at non-primes. -/
theorem isUnramifiedAt_of_not_prime {p : ℕ} [Fact (Nat.Prime p)]
    (ρ : GaloisRep 2 (ZMod p) ℚ) (ℓ : ℕ) (h : ¬Nat.Prime ℓ) :
    IsUnramifiedAt ρ ℓ := by
  intro hℓ; exact absurd hℓ h

end Fermat
