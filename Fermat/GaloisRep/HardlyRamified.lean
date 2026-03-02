/-
  Hardly Ramified Representations and the Galois-Theoretic Contradiction (WP8)

  Formalizes the "hardly ramified" condition on mod-p Galois representations
  (Imperial FLT Blueprint: Chapter 3, Theorem 3.3) and derives the
  Galois-theoretic contradiction at the heart of FLT.

  A representation ρ : Gal(Q̄/Q) → GL₂(𝔽_p) is "hardly ramified" if:
    (1) det(ρ) = χ_p (the mod-p cyclotomic character)
    (2) ρ is unramified outside {2, p}
    (3) ρ|_{Gal(Q̄₂/Q₂)} is reducible with unramified quotient of square 1
    (4) ρ|_{Gal(Q̄_p/Q_p)} arises from a finite flat group scheme

  The two key results:
  • Theorem 3.3 (frey_rep_hardly_ramified): The Frey curve's mod-p
    representation is hardly ramified. DECOMPOSED into 4 sub-results:
    (1) Weil pairing → cyclotomic det: PROVED from `galRep_det`
    (2) Ramification analysis → unramified outside {2,p}: PROVED from
        `Discriminant.frey_rep_unramified_all_odd` (which uses tate_unramified)
    (3) Tate's algorithm at 2 → locally reducible: SUB-AXIOM
    (4) Fontaine/Raynaud → flat at p: SUB-AXIOM

  • Theorem 3.4 (hardly_ramified_reducible): Every hardly ramified
    representation is reducible. This is the deep result — it follows
    from Serre's conjecture (partial cases proved by Langlands–Tunnell)
    combined with class field theory.

  The contradiction: Mazur's theorem (galRep_irreducible_frey) says the
  Frey representation is irreducible, while 3.3 + 3.4 say it is reducible.
  This proves FLT for primes p ≥ 5 via a purely Galois-theoretic route.

  Imperial FLT Blueprint: Chapter 3, §3.3–3.4.
-/

import Fermat.Modularity.Ribet

set_option linter.dupNamespace false

namespace Fermat

open Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Sub-predicates for "Hardly Ramified"
-- ═══════════════════════════════════════════════════════════════════════════

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The determinant of ρ equals the mod-p cyclotomic character χ_p.

For the mod-p representation attached to an elliptic curve, this is the
Weil pairing (axiomatized as `galRep_det` in EllipticCurve.lean). For a
general representation, this constrains the 1-dimensional information
(the "central character") of the 2-dimensional representation. -/
def HasCyclotomicDet (ρ : GaloisRep 2 (ZMod p) ℚ) : Prop :=
  GaloisRep.det ρ = cyclotomicChar p

/-- The representation ρ is unramified at every prime q ∉ {2, p}.

For the Frey curve y² = x(x − aᵖ)(x + bᵖ), the discriminant is
Δ = 2⁸(abc)^{2p}. At an odd prime ℓ ≠ p dividing abc, the Frey curve
has multiplicative reduction with p | v_ℓ(Δ), so the mod-p
representation is unramified (the inertia action has order dividing
v_ℓ(Δ), which is 0 mod p). At primes not dividing 2·p·abc, the curve
has good reduction and the representation is automatically unramified.
-/
def IsUnramifiedOutside2p
    (ρ : GaloisRep 2 (ZMod p) ℚ) : Prop :=
  ∀ (q : ℕ), Nat.Prime q → q ≠ 2 → q ≠ p → IsUnramifiedAt ρ q

/-- The restriction of ρ to the decomposition group at 2 is reducible,
with an unramified quotient whose square is the identity.

For the Frey curve, the local representation at 2 comes from the Tate
parametrization (since the Frey curve has multiplicative reduction at
2). The unramified quotient is the unramified character sending Frob₂
to ±1 (the Legendre symbol of the discriminant). The "square 1"
condition means this character has order dividing 2.

Opaque because the decomposition group D₂ ⊂ Gal(Q̄/Q) requires:
1. A choice of prime above 2 in Z̄ (determines the embedding Q̄ ↪ Q̄₂)
2. The local Galois group Gal(Q̄₂/Q₂) and its inertia filtration
3. The restriction functor from global to local representations -/
opaque IsLocallyReducibleAt2
    (ρ : GaloisRep 2 (ZMod p) ℚ) : Prop

/-- The restriction of ρ to the decomposition group at p arises from a
finite flat group scheme over ℤ_p.

This is the "flatness" condition from Fontaine's theory: the p-torsion
E[p] of the Frey curve, when base-changed to ℚ_p, extends to a finite
flat group scheme over ℤ_p. For p ≥ 3, this is equivalent to saying
that E has good reduction at p, or (for multiplicative reduction) that
the representation is "ordinary" in the sense of Fontaine–Laffaille.

For the Frey curve at primes p ≥ 5 not dividing abc, this follows from
good reduction. For p | abc, it follows from the theory of
Barsotti–Tate groups.

Opaque because the finite flat group scheme condition requires:
1. p-divisible groups and Fontaine's classification
2. The integral model of E over ℤ_p
3. Raynaud's theorem on finite flat group schemes -/
opaque IsFlatAtP
    (ρ : GaloisRep 2 (ZMod p) ℚ) : Prop

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The "Hardly Ramified" Predicate
-- ═══════════════════════════════════════════════════════════════════════════

/-- A mod-p Galois representation ρ : Gal(Q̄/Q) → GL₂(𝔽_p) is **hardly
ramified** if it satisfies all four conditions:

  (1) det(ρ) = χ_p — the cyclotomic determinant condition
  (2) ρ is unramified outside {2, p}
  (3) ρ|_{D₂} is reducible with unramified quotient of square 1
  (4) ρ|_{D_p} is flat (arises from a finite flat group scheme)

This definition isolates the precise local-global conditions on the Frey
curve's mod-p representation that, combined with Serre's conjecture /
Langlands–Tunnell, force reducibility.

The term "hardly ramified" is from the Imperial FLT Blueprint: a
representation that is ramified at very few primes (only 2 and p) and
even at those primes has controlled ramification behavior.

Imperial FLT Blueprint: Chapter 3, Definition 3.2. -/
def IsHardlyRamified
    (ρ : GaloisRep 2 (ZMod p) ℚ) : Prop :=
  HasCyclotomicDet ρ ∧
  IsUnramifiedOutside2p ρ ∧
  IsLocallyReducibleAt2 ρ ∧
  IsFlatAtP ρ

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Theorem 3.3 — The Frey Representation is Hardly Ramified (Decomposed)
-- ═══════════════════════════════════════════════════════════════════════════

/-
  DECOMPOSITION STRATEGY.

  The monolithic axiom `frey_rep_hardly_ramified` asserted all four conditions
  of `IsHardlyRamified` at once. We decompose it into four sub-results:

  (1) HasCyclotomicDet — PROVED from `galRep_det` (Weil pairing axiom)
  (2) IsUnramifiedOutside2p — PROVED from
      `Discriminant.frey_rep_unramified_all_odd` (which uses tate_unramified)
  (3) IsLocallyReducibleAt2 — SUB-AXIOM (opaque predicate, requires Tate curve)
  (4) IsFlatAtP — SUB-AXIOM (opaque predicate, requires Fontaine theory)

  Net effect: the axiom `frey_rep_hardly_ramified` becomes a *proved theorem*
  composed from 2 proved lemmas + 2 sub-axioms. The `tate_unramified` axiom
  in Discriminant.lean (which also powers frey_rep_unramified) is the only
  new axiom, and it is a general statement about Tate parametrization.
-/

-- ─────────────────────────────────────────────────────────────────────────
-- §3a. Condition 1: Cyclotomic Determinant (PROVED)
-- ─────────────────────────────────────────────────────────────────────────

/-- **Theorem (Condition 1).** The mod-p Galois representation of the
Frey curve has cyclotomic determinant: det(ρ̄_{E,p}) = χ_p.

Proof: immediate from the Weil pairing (`galRep_det`) applied to the
Frey curve, using `frey_discriminant` to verify Δ ≠ 0.

Imperial FLT Blueprint: Chapter 3, §3.2 (Weil pairing). -/
theorem frey_has_cyclotomic_det (a b c : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasCyclotomicDet (galRepOfCurve (freyCurve a b p) p) := by
  unfold HasCyclotomicDet
  exact galRep_det (freyCurve a b p) p hp5
    (frey_discriminant a b c p hp5 heq ha hb hc)

-- ─────────────────────────────────────────────────────────────────────────
-- §3b. Condition 2: Unramified Outside {2, p} (PROVED)
-- ─────────────────────────────────────────────────────────────────────────

/-- **Theorem (Condition 2).** The mod-p Galois representation of the
Frey curve is unramified at every prime q with q ≠ 2 and q ≠ p.

Proof: `Discriminant.frey_rep_unramified_all_odd` provides unramifiedness
at ALL odd primes (not just those dividing the conductor), using the
Tate parametrization axiom and the fact that p | v_q(Δ) for the Frey
curve's discriminant Δ = 16(abc)^{2p}. Since IsUnramifiedOutside2p
requires q ≠ 2 and q ≠ p, and "odd" = "≠ 2", the q = p case is
excluded by hypothesis, so we just apply the general result.

Imperial FLT Blueprint: Chapter 3, §3.2 (ramification analysis). -/
theorem frey_unramified_outside_2p (a b c : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsUnramifiedOutside2p (galRepOfCurve (freyCurve a b p) p) := by
  unfold IsUnramifiedOutside2p
  intro q hq hq2 _hqp
  exact Discriminant.frey_rep_unramified_all_odd a b c p hp5 heq
    ha hb hc q hq hq2

-- ─────────────────────────────────────────────────────────────────────────
-- §3c. Conditions 3 & 4: Sub-axioms (opaque predicates)
-- ─────────────────────────────────────────────────────────────────────────

/-- **Axiom (Condition 3: Tate's algorithm at 2).** The mod-p Galois
representation of the Frey curve is locally reducible at 2.

The Frey curve y² = x(x − aᵖ)(x + bᵖ) has multiplicative reduction at 2
(the normalized form has 2 | Δ). By the Tate parametrization, the local
representation at 2 is an extension of an unramified character by the
cyclotomic character. The unramified quotient sends Frob₂ to ±1 (the
Legendre symbol of the Tate parameter), so its square is 1.

Proving this formally requires:
1. Tate's algorithm to determine the reduction type at 2
2. The Tate parametrization for multiplicative reduction
3. The structure of the local representation ρ̄|_{D₂}

Imperial FLT Blueprint: Chapter 3, Theorem 3.3(3). -/
axiom frey_locally_reducible_at_2 (a b c : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsLocallyReducibleAt2 (galRepOfCurve (freyCurve a b p) p)

/-- **Axiom (Condition 4: Fontaine flatness).** The mod-p Galois
representation of the Frey curve is flat at p.

For the Frey curve E at a prime p ≥ 5:
• If p ∤ abc: E has good reduction at p, so E[p] extends to a finite
  flat group scheme over ℤ_p (the p-torsion of the Néron model).
• If p | abc: E has multiplicative reduction at p, but Raynaud's theorem
  (applied because p ≥ 3 and E is semistable) still gives a finite
  flat group scheme structure on E[p] over ℤ_p.

Proving this formally requires:
1. Fontaine's classification of finite flat group schemes over ℤ_p
2. Raynaud's theorem on prolongation of group schemes
3. The theory of Barsotti–Tate groups for semistable curves

Imperial FLT Blueprint: Chapter 3, Theorem 3.3(4). -/
axiom frey_flat_at_p (a b c : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsFlatAtP (galRepOfCurve (freyCurve a b p) p)

-- ─────────────────────────────────────────────────────────────────────────
-- §3d. Assembly: The Frey Representation is Hardly Ramified (PROVED)
-- ─────────────────────────────────────────────────────────────────────────

/-- **Theorem (Theorem 3.3).** The mod-p Galois representation of the Frey
curve attached to a putative FLT counterexample a^p + b^p = c^p is
hardly ramified.

Previously a monolithic axiom; now a proved composition:
(1) `frey_has_cyclotomic_det` — from `galRep_det` (Weil pairing) [PROVED]
(2) `frey_unramified_outside_2p` — from
    `Discriminant.frey_rep_unramified_all_odd` [PROVED]
(3) `frey_locally_reducible_at_2` — Tate's algorithm [SUB-AXIOM]
(4) `frey_flat_at_p` — Fontaine/Raynaud flatness [SUB-AXIOM]

Imperial FLT Blueprint: Chapter 3, Theorem 3.3. -/
theorem frey_rep_hardly_ramified (a b c : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsHardlyRamified (galRepOfCurve (freyCurve a b p) p) :=
  ⟨frey_has_cyclotomic_det a b c p hp5 heq ha hb hc,
   frey_unramified_outside_2p a b c p hp5 heq ha hb hc,
   frey_locally_reducible_at_2 a b c p hp5 heq ha hb hc,
   frey_flat_at_p a b c p hp5 heq ha hb hc⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Theorem 3.4 — Hardly Ramified Implies Reducible
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Theorem 3.4).** A hardly ramified mod-p Galois representation
with p ≥ 5 is reducible (i.e., NOT irreducible).

This is the deepest result in the Galois-theoretic approach to FLT.
The proof combines:

1. **Serre's conjecture (partial cases):** If ρ̄ is irreducible and
   hardly ramified, then by Serre's recipe the predicted weight is 2
   and the predicted level is 1 (since ρ̄ is unramified outside {2,p}
   and has controlled behavior at 2 and p).

2. **Langlands–Tunnell theorem:** For p = 3, the projective image of
   ρ̄ lands in PGL₂(𝔽₃) ≅ S₄, and the Langlands–Tunnell theorem
   (solvable base change) proves the corresponding modular form exists.

3. **No weight-2 forms at level 1:** S₂(SL₂(ℤ)) = 0 (the modular
   curve X₀(1) has genus 0), so no such modular form can exist.

4. **Contradiction:** Steps 1–3 show that no irreducible hardly
   ramified representation exists for p ≥ 5, i.e., every such
   representation is reducible.

Imperial FLT Blueprint: Chapter 3, Theorem 3.4. -/
axiom hardly_ramified_reducible (p : ℕ) [Fact (Nat.Prime p)]
    (ρ : GaloisRep 2 (ZMod p) ℚ)
    (hp5 : p ≥ 5)
    (hhr : IsHardlyRamified ρ) :
    ¬ GaloisRep.IsIrreducible ρ

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. The Frey Representation is Reducible (PROVED)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem.** The mod-p Galois representation of the Frey curve is
reducible.

Proof: compose Theorem 3.3 (the Frey representation is hardly ramified)
with Theorem 3.4 (hardly ramified implies reducible).

This is the Galois-theoretic half of the contradiction. The other half
is Mazur's theorem (`galRep_irreducible_frey`): the same representation
is irreducible. -/
theorem frey_rep_reducible (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬ GaloisRep.IsIrreducible
      (galRepOfCurve (freyCurve a b p) p) :=
  hardly_ramified_reducible p
    (galRepOfCurve (freyCurve a b p) p) hp5
    (frey_rep_hardly_ramified a b c p hp5 heq ha hb hc)

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. FLT from Galois Representations (PROVED)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (FLT for primes p ≥ 5, Galois-theoretic route).**

There is no nonzero integer solution to a^p + b^p = c^p for p ≥ 5 prime.

Proof:
1. Assume a^p + b^p = c^p with a, b, c ≠ 0 and p ≥ 5 prime.
2. Construct the Frey curve E : y² = x(x − aᵖ)(x + bᵖ).
3. By Mazur's theorem (`galRep_irreducible_frey`), ρ̄_{E,p} is
   irreducible.
4. By Theorems 3.3 + 3.4 (`frey_rep_reducible`), ρ̄_{E,p} is reducible.
5. Irreducible ∧ ¬Irreducible = False.

This is the purely Galois-theoretic proof of FLT, avoiding the
modularity lifting → level lowering → genus formula route. It replaces
the Ribet contradiction chain (`ribet_contradiction` in Ribet.lean)
with the more direct Mazur vs. Serre/Langlands–Tunnell contradiction.

The two routes to FLT share:
- Frey curve construction (FreyCurve.lean)
- Mazur's irreducibility theorem (EllipticCurve.lean)

They differ in how they obtain reducibility:
- Ribet route:   modularity → level lowering → no cusp forms at level 2
- Galois route:  hardly ramified → Serre conjecture → no forms at level 1

Imperial FLT Blueprint: Chapter 3, §3.3–3.4 (this route). -/
theorem flt_from_galois_reps (a b c : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : False := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Mazur: the Frey representation is irreducible
  have hirr :
      GaloisRep.IsIrreducible (galRepOfCurve (freyCurve a b p) p) :=
    galRep_irreducible_frey a b c p hp5 heq ha hb hc
  -- Serre/Langlands-Tunnell: the Frey representation is reducible
  have hred :
      ¬ GaloisRep.IsIrreducible
        (galRepOfCurve (freyCurve a b p) p) :=
    frey_rep_reducible a b c p hp5 heq ha hb hc
  -- Contradiction
  exact hred hirr

-- ═══════════════════════════════════════════════════════════════════════════
-- Summary of axiom budget
-- ═══════════════════════════════════════════════════════════════════════════

/-
  PROVED (0 sorry):
  • frey_has_cyclotomic_det        [§3a]
    From galRep_det (Weil pairing) + frey_discriminant (Δ ≠ 0).
  • frey_unramified_outside_2p     [§3b]
    From Discriminant.frey_rep_unramified_all_odd (tate_unramified axiom).
  • frey_rep_hardly_ramified       [§3d, was axiom, now theorem]
    Composition of conditions 1–4.
  • frey_rep_reducible             [§5]
    Composition: Theorem 3.3 + Theorem 3.4 → ¬IsIrreducible
  • flt_from_galois_reps           [§6]
    Composition: Mazur (irreducible) + §5 (reducible) → False

  AXIOMS (3, was 2 — but more transparent):
  • frey_locally_reducible_at_2    [§3c, split from frey_rep_hardly_ramified]
    Tate's algorithm at 2. Requires Tate parametrization for local rep at 2.

  • frey_flat_at_p                 [§3c, split from frey_rep_hardly_ramified]
    Fontaine/Raynaud flatness. Requires p-divisible group theory.

  • hardly_ramified_reducible      [§4, unchanged]
    Deepest axiom: Serre's conjecture (partial) + Langlands–Tunnell.
    Requires automorphic forms + class field theory.

  SHARED AXIOM (from Discriminant.lean):
  • tate_unramified — used by frey_unramified_outside_2p via
    Discriminant.frey_rep_unramified_all_odd. General statement about
    the Tate parametrization: p | v_ℓ(Δ) → mod-p rep unramified at ℓ.

  OPAQUE (2, unchanged):
  • IsLocallyReducibleAt2          [§1]
    Local reducibility at 2. Requires decomposition groups.

  • IsFlatAtP                      [§1]
    Fontaine flatness. Requires p-divisible group theory.

  NET EFFECT:
  The monolithic `frey_rep_hardly_ramified` axiom (1 axiom asserting a
  4-way conjunction) is replaced by:
    • 2 proved lemmas (conditions 1–2)
    • 2 sub-axioms (conditions 3–4)
    • 1 proved assembly theorem

  The axiom count increases from 2 to 3 in this file (plus tate_unramified
  shared with the Ribet route), but the *opaque content* decreases:
  conditions 1 and 2 are now visible to the kernel. The new axioms are
  individually more transparent and independently verifiable:
    • frey_locally_reducible_at_2 is Tate's algorithm (explicit computation)
    • frey_flat_at_p is Raynaud's theorem (deep but standard)

  An independent proof of FLT for p ≥ 5 via Galois representations,
  parallel to the modularity route in Ribet.lean. Both routes share
  Mazur's irreducibility but derive reducibility differently:
    Ribet route:   modularity → level lowering → no cusp forms at level 2
    Galois route:  hardly ramified → Serre conjecture → no forms at level 1
-/

end Fermat
