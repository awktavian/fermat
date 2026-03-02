# Plan: Mathlib Infrastructure for Eliminating 12 FLT Axioms

## Context

The `~/fermat` repo formalizes Fermat's Last Theorem in Lean 4 (v4.28.0, Mathlib via flt-regular). Current state: **0 sorry, 12 axioms**. 15 axioms were eliminated in prior work via Mathlib instances, type strengthening, derivation from other axioms, and concretizing local opaque types.

The remaining 12 axioms all reference **shared opaque definitions** (`galRepOfCurve`, `galRepOfNewform`, `cyclotomicChar`, `conductorOf`, `IsUnramifiedAt`, etc.) that cannot be concretized without building real mathematical infrastructure. This plan maps out the Mathlib-level work needed to prove each axiom, organized as work packages with dependency ordering.

**This is a multi-session, multi-month effort.** The plan is designed so each session produces a self-contained, compilable artifact that makes permanent progress.

---

## The 12 Axioms

| # | Axiom | File | Mathematical Content |
|---|-------|------|---------------------|
| A1 | `torsion_dim` | EllipticCurve.lean:104 | E[p] ≅ (𝔽_p)² |
| A2 | `galRep_det` | EllipticCurve.lean:118 | det(ρ_{E,p}) = χ_p (Weil pairing) |
| A3 | `galRep_irreducible_frey` | EllipticCurve.lean:144 | Mazur: Frey ρ irreducible for p≥5 |
| B1 | `frey_conductor_eq` | Conductor.lean:105 | Conductor = rad(\|abc\|) |
| B2 | `frey_rep_unramified` | Ribet.lean:115 | Frey unramified at odd ℓ\|N |
| B3 | `frey_rep_hardly_ramified` | HardlyRamified.lean:156 | 4 local conditions on Frey curve |
| C1 | `dim_cusp_forms_weight2` | RiemannRoch.lean:75 | dim S₂(Γ₀(N)) = genus(X₀(N)) |
| C2 | `cusp_forms_finite` | RiemannRoch.lean:82 | S₂(Γ₀(N)) finite-dimensional |
| C3 | `newform_from_modular_curve` | Newform.lean:128 | Eichler-Shimura direction |
| C4 | `galRep_of_newform_irreducible` | Newform.lean:148 | Newform ρ irreducible for p≥5 |
| D1 | `ribet_level_lowering` | Ribet.lean:85 | Ribet 1990: level descent |
| D2 | `hardly_ramified_reducible` | HardlyRamified.lean:190 | Serre + Langlands-Tunnell |

---

## Dependency Graph

```
WP-CYC (cyclotomicChar)              WP-RAM (IsUnramifiedAt)
     │                                    │
     ▼                                    ▼
WP-TORS (p-torsion) ──► WP-GALREP ──► WP-UNRAM (B2) ──► WP-COND (B1)
     │                    (galRepOfCurve)      │
     ▼                       │                 ▼
  A1 proved                  ▼            WP-HARDY (B3, partial)
                        WP-WEIL (A2)
                             │
                             ▼
                    ┌── TIER 4 (BLOCKED) ──┐
                    │  A3: Mazur           │
                    │  C3: Eichler-Shimura │    WP-CUSP (C1, C2)
                    │  C4: depends on C3   │         │
                    │  D1: Ribet           │    C1, C2 proved
                    │  D2: Serre/LT        │
                    └──────────────────────┘
```

---

## Work Packages

### WP-CYC: Cyclotomic Character Bridge
**Eliminates**: Unblocks A2 (with WP-WEIL)
**Effort**: ~200-400 lines, 1-2 sessions
**File**: `Fermat/Mathlib/CyclotomicBridge.lean`

Replace opaque `cyclotomicChar` with concrete definition using Mathlib's existing `cyclotomicCharacter`:

1. `Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter` provides `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ`
2. Bridge: `AbsGaloisGroup ℚ` → `AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ` (via `AlgEquiv.toRingEquiv`)
3. Compose with mod-p reduction `ℤ_[p]ˣ →* (ZMod p)ˣ` (via `PadicInt.toZModPow 1`)
4. Show `AlgebraicClosure ℚ` has enough roots of unity (from `IsAlgClosed.exists_primitiveRoot`)

**Mathlib refs**: `Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter`, `Mathlib.FieldTheory.AbsoluteGaloisGroup`

---

### WP-RAM: Ramification Infrastructure
**Eliminates**: Unblocks B1, B2, B3
**Effort**: ~400-700 lines, 2-3 sessions
**File**: `Fermat/Mathlib/InertiaGroups.lean`

Concretize opaque `IsUnramifiedAt` using Mathlib's decomposition/inertia groups:

1. Extend ℓ-adic valuation to `AlgebraicClosure ℚ` (Zorn's lemma via `Valuation.extension`)
2. Extract `decompositionSubgroup` and `inertiaSubgroup` from `Mathlib.RingTheory.Valuation.RamificationGroup`
3. Embed into `AbsGaloisGroup ℚ` via inclusion chain
4. Define `IsUnramifiedAt ρ ℓ := ∀ σ ∈ inertiaGroupAt ℓ, ρ.toMonoidHom σ = 1`

**Mathlib refs**: `Mathlib.RingTheory.Valuation.RamificationGroup` (decompositionSubgroup, inertiaSubgroup), `Mathlib.NumberTheory.RamificationInertia.Basic`

---

### WP-TORS: EC p-Torsion Structure Theorem
**Eliminates**: A1 (torsion_dim)
**Effort**: ~500-800 lines, 3-4 sessions
**File**: `Fermat/Mathlib/ECTorsion.lean`

Prove E[p] ≅ (ℤ/pℤ)² over algebraically closed fields:

1. Define `pTorsion W p := { P : W⟮F⟯ | (p : ℤ) • P = 0 }` using Mathlib's `WeierstrassCurve.Affine.Point` group law
2. Show `|E[p]| = p²` via division polynomial `ψ_p` (degree `(p²-1)/2` from `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`)
3. Apply finite abelian p-group structure theorem: killed by p + order p² → isomorphic to (ℤ/pℤ)²

**Mathlib refs**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` (AddCommGroup), `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (natDegree_preΨ)

---

### WP-GALREP: Galois Representation Construction
**Eliminates**: Unblocks A2, A3, B1, B2, B3
**Dependencies**: WP-TORS, WP-CYC
**Effort**: ~600-1000 lines, 3-5 sessions
**File**: `Fermat/Mathlib/GalRepConstruction.lean`

Concretize opaque `galRepOfCurve` — the mod-p Galois representation from an elliptic curve:

1. Galois group acts on `E(AlgebraicClosure ℚ)` by acting on coordinates
2. Action preserves group law (Weierstrass equation has ℚ-coefficients)
3. Action restricts to `E[p]` (preserves p-torsion)
4. Choose basis of `E[p] ≅ (𝔽_p)²` → get `ρ : Gal(ℚ̄/ℚ) → GL₂(𝔽_p)`
5. Verify continuity (finite image → open kernel → continuous)

**Key challenge**: Lean formalization of "σ acts on coordinates" through the ideal class group construction. May need `WeierstrassCurve.Affine.Point.map` or explicit coordinate action.

---

### WP-WEIL: Weil Pairing → galRep_det
**Eliminates**: A2 (galRep_det)
**Dependencies**: WP-GALREP, WP-CYC
**Effort**: ~800-1500 lines, 5-8 sessions
**File**: `Fermat/Mathlib/WeilPairing.lean`

Construct the Weil pairing e_p : E[p] × E[p] → μ_p and prove det(ρ) = χ_p:

1. Define e_p via Miller's algorithm (algebraic, avoids Riemann-Roch for curves)
2. Prove bilinearity, alternating, non-degeneracy
3. Prove Galois equivariance: e_p(σP, σQ) = σ(e_p(P,Q))
4. Derive: det(ρ)(σ) = χ_p(σ) from equivariance + non-degeneracy

**Hardest part**: Miller's algorithm requires the function field of E, which needs `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` function field or explicit rational function construction.

---

### WP-UNRAM: Frey Curve Unramifiedness
**Eliminates**: B2 (frey_rep_unramified)
**Dependencies**: WP-RAM, WP-GALREP
**Effort**: ~400-600 lines, 2-3 sessions
**File**: `Fermat/Mathlib/FreyUnramified.lean`

Explicit computation: for odd ℓ | abc, the Frey curve's mod-p rep is unramified at ℓ:

1. Compute v_ℓ(Δ) for Frey curve Δ = 2⁸(abc)^{2p}: v_ℓ(Δ) = 2p·v_ℓ(abc)
2. Show p | v_ℓ(Δ) since p ≥ 5
3. Tate parametrization: inertia action has order dividing v_ℓ(Δ)
4. Since p | v_ℓ(Δ), the mod-p inertia action is trivial → unramified

---

### WP-COND: Artin Conductor Formula
**Eliminates**: B1 (frey_conductor_eq)
**Dependencies**: WP-RAM, WP-GALREP
**Effort**: ~500-800 lines, 3-5 sessions
**File**: `Fermat/Mathlib/ConductorFormula.lean`

Define and compute the Artin conductor:

1. Define `conductorExponent ρ ℓ := codim V^{I_ℓ}` (no Swan conductor for semistable)
2. For Frey at odd ℓ | abc: multiplicative reduction → conductor exponent = 1
3. For Frey at ℓ ∤ 2abc: good reduction → conductor exponent = 0
4. Product formula: conductor = ∏_{ℓ | abc, odd} ℓ · (2-adic factor) = rad(abc) (simplified)

---

### WP-CUSP: Cusp Form Dimension Theory
**Eliminates**: C1 (dim_cusp_forms_weight2), C2 (cusp_forms_finite)
**Dependencies**: None (independent track)
**Effort**: ~1000-2000 lines, 5-10 sessions
**File**: `Fermat/Mathlib/CuspFormDimension.lean`

Two sub-goals:

**C2 (finite-dimensionality)**: Multiple possible approaches:
- Fourier expansion: cusp forms → bounded Fourier coefficients → finite-dimensional (uses Hecke's bound from `Mathlib.NumberTheory.ModularForms.Bounds`)
- Compactness: fundamental domain of Γ₀(N)\H is compact (modulo cusps) → space of bounded holomorphic functions is finite-dimensional

**C1 (dimension = genus)**: Requires identifying weight-2 cusp forms with holomorphic differentials on X₀(N). Two approaches:
- Analytic: S₂(Γ₀(N)) ≅ H⁰(X₀(N), Ω¹) via f(τ) ↦ f(τ)dτ, then Riemann-Roch gives dim = genus
- For N=2 specifically: could try to show directly that every weight-2 cusp form for Γ₀(2) vanishes (since genus = 0, no nonzero differentials exist)

**Mathlib TODO**: `LevelOne.lean` contains `-- TODO: Add finite-dimensionality of these spaces of modular forms.` — this is a known gap.

---

### TIER 4: Blocked Axioms (Imperial FLT alignment)

These 5 axioms require infrastructure that is years away from formalization:

| Axiom | Required Theory | Imperial FLT Status | Timeline |
|-------|----------------|--------------------|---------|
| A3: `galRep_irreducible_frey` | Mazur's theorem (geometry of X₀(p)) | Deferred | 2029+ |
| C3: `newform_from_modular_curve` | Eichler-Shimura (Jacobian J₀(N), Hecke operators) | Chapters 5-6 in progress | 2027-2029 |
| C4: `galRep_of_newform_irreducible` | Depends on C3 + Mazur | Deferred | 2029+ |
| D1: `ribet_level_lowering` | Mazur's principle, Ihara's lemma | Deferred to Phase 2 | 2029+ |
| D2: `hardly_ramified_reducible` | Serre's conjecture, Langlands-Tunnell | Not on any roadmap | 2032+ |

**Strategy**: Wait for Imperial FLT to formalize these, then import their theorems. Contribute upstream where possible (WP-CYC, WP-RAM, WP-TORS are Mathlib-quality contributions).

---

## Session Schedule

### Phase 1: Foundation (Sessions 1-5)
| Session | WP | Axioms Eliminated | Cumulative |
|---------|-----|-------------------|-----------|
| 1 | WP-CYC | 0 (infrastructure) | 12 |
| 2-3 | WP-RAM | 0 (infrastructure) | 12 |
| 4-5 | WP-TORS | 1 (torsion_dim) | 11 |

### Phase 2: Galois Representations (Sessions 6-12)
| Session | WP | Axioms Eliminated | Cumulative |
|---------|-----|-------------------|-----------|
| 6-8 | WP-GALREP | 0 (infrastructure) | 11 |
| 9-10 | WP-UNRAM | 1 (frey_rep_unramified) | 10 |
| 11-12 | WP-COND | 1 (frey_conductor_eq) | 9 |

### Phase 3: Deep Results (Sessions 13-25)
| Session | WP | Axioms Eliminated | Cumulative |
|---------|-----|-------------------|-----------|
| 13-17 | WP-WEIL | 1 (galRep_det) | 8 |
| 18-22 | WP-CUSP | 2 (cusp_forms_finite, dim_cusp_forms_weight2) | 6 |
| 23-25 | WP-HARDY (partial) | 0-1 (frey_rep_hardly_ramified, conditions 1-2 only) | 5-6 |

### Phase 4: External (2029+)
| Source | Axioms Eliminated | Cumulative |
|--------|-------------------|-----------|
| Imperial FLT Phase 1 | 3-4 (Mazur, Eichler-Shimura, Ribet) | 1-2 |
| Imperial FLT Phase 2 | 1-2 (Serre/LT) | 0 |

---

## Projected Axiom Count

```
Now:          12  ████████████
Session 5:    11  ███████████
Session 12:    9  █████████
Session 17:    8  ████████
Session 22:    6  ██████
Session 25:   5-6 █████▒
Imperial P1:  1-2 █▒
Imperial P2:    0  ✓
```

---

## Verification Strategy

After each work package:
1. `lake build Fermat` — 0 errors
2. `grep -rn "^axiom " Fermat/ | grep -v ".lake" | wc -l` — axiom count decreased
3. `lake build Fermat 2>&1 | grep -i sorry` — 0 sorry
4. `#print axioms <theorem_name>` — verify no unexpected axioms in the proof

---

## Critical Files

| File | Role |
|------|------|
| `Fermat/GaloisRep/EllipticCurve.lean` | Opaques: galRepOfCurve, cyclotomicChar, torsionModule. Axioms: A1-A3 |
| `Fermat/GaloisRep/HardlyRamified.lean` | Opaques: IsLocallyReducibleAt2, IsFlatAtP. Axioms: B3, D2 |
| `Fermat/GaloisRep/Conductor.lean` | Opaque: conductorOf. Axiom: B1 |
| `Fermat/Modularity/Ribet.lean` | Opaque: IsUnramifiedAt. Axioms: B2, D1 |
| `Fermat/ModularForms/RiemannRoch.lean` | Axioms: C1, C2 |
| `Fermat/ModularForms/Newform.lean` | Opaque: galRepOfNewform. Axioms: C3, C4 |
| `.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` | Existing cyclotomicCharacter |
| `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean` | Existing decomposition/inertia groups |
| `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` | EC group law |
| `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` | Division polynomial degrees |
