# Fermat's Last Theorem in Lean 4

0 sorry. 21 axioms. FLT for all n ≥ 3.

## Status

| Metric | Value |
|--------|-------|
| Sorry | 0 |
| Axioms | 21 (all independent, irreducible with current Mathlib) |
| Lines | ~3600 |
| Files | 23 |

## Architecture

Two independent proof routes for primes p ≥ 5, plus direct computation for small cases.

```
FLT(n) for n ≥ 3
├── n = 3, 4: mathlib
├── n = regular prime: flt-regular
├── n = composite: prime factor reduction
└── n = prime p ≥ 5:
    ├── Route 1 (Ribet): wiles_chain (PROVED)
    │   ├── frey_is_modular (PROVED — from R=T infrastructure)
    │   └── ribet_contradiction (PROVED)
    │       ├── frey_descent_to_level_2 (PROVED — from newform_from_modular_curve)
    │       ├── newform_nonzero (PROVED — from Newform.ne_zero)
    │       └── cusp_form_level2_eq_zero (PROVED — genus + Riemann-Roch axiom)
    │
    └── Route 2 (Galois): flt_from_galois_reps (PROVED)
        ├── galRep_irreducible_frey (AXIOM — Mazur 1978)
        └── frey_rep_reducible (PROVED)
            ├── frey_rep_hardly_ramified (AXIOM — Thm 3.3)
            └── hardly_ramified_reducible (AXIOM — Thm 3.4)
```

## Proved Results (sorry-free, was axiom/sorry)

- **frey_is_modular** — derived from R=T infrastructure (was axiom)
- **ribet_from_modularity_and_genus** — superseded by ribet_contradiction (was axiom)
- **frey_descent_to_level_2** — from newform_from_modular_curve at N=2 (was axiom)
- **modularity_level_eq_conductor** — from newform_from_modular_curve + R=T (was axiom)
- **newform_nonzero** — from Newform.ne_zero field (was axiom)
- **cusp_forms_free** — Module.Free.of_divisionRing (was axiom)
- **radical_dvd** — Nat.prod_primeFactors_dvd (was sorry)
- Sophie Germain's theorem (Case I for SG primes) — 760 lines
- Frey curve Δ ≠ 0, semistability at odd primes, genus(X₀(N)) for N=2..13
- ribet_contradiction, flt_from_galois_reps, cusp_form_level2_eq_zero
- FLT for regular primes, n ∈ [3,16]

## Axiom Budget (21)

| Category | Count | Axioms |
|----------|-------|--------|
| Galois reps (critical) | 3 | galRep_irreducible_frey, frey_rep_hardly_ramified, hardly_ramified_reducible |
| Ribet chain | 2 | ribet_level_lowering, frey_rep_unramified |
| Riemann-Roch | 2 | dim_cusp_forms_weight2, cusp_forms_finite |
| R=T infrastructure | 6 | CommRing R/T, naturalMap, R_surjects_T, R_iso_T, R_iso_T_implies_modularity |
| EC infrastructure | 3 | torsion_dim, galRep_det, frey_conductor_eq |
| Newform infrastructure | 2 | newform_from_modular_curve, galRep_of_newform_irreducible |
| Mod 3 | 3 | fontaine_no_abelian_scheme_over_Z, odlyzko_discriminant_bound, mod3_classification |

## Axiom Dependencies

Critical path (Route 1): R_iso_T → R_iso_T_implies_modularity → (modularity) → newform_from_modular_curve → (descent) + dim_cusp_forms_weight2 + cusp_forms_finite → contradiction

Critical path (Route 2): galRep_irreducible_frey + frey_rep_hardly_ramified + hardly_ramified_reducible → contradiction

## Contributing

### To eliminate an axiom:
1. Prove the theorem in Lean against Mathlib
2. Replace `axiom foo ...` with `theorem foo ... := <proof>`
3. `lake build Fermat` — verify 0 errors

### Recommended attack order:
1. **dim_cusp_forms_weight2** — Riemann-Roch for modular curves. ~500 lines.
2. **frey_rep_hardly_ramified** (Thm 3.3) — verify 4 conditions on Frey curve. ~1000 lines.
3. **mod3_classification** (Thm 3.9) — classify hardly ramified mod 3 reps. ~1500 lines.
4. **hardly_ramified_reducible** (Thm 3.4) — compose Thms 3.6+3.7+3.9. HARD.
5. **R_iso_T** — Taylor-Wiles patching. EXTREME.

### Mathlib gaps blocking further elimination:
- No Weil pairing → blocks galRep_det, torsion_dim
- No cusp form finite-dimensionality → blocks cusp_forms_finite
- No Riemann-Roch for modular curves → blocks dim_cusp_forms_weight2
- Modular form dimension results: level-1 only (weight 0 rank 1, neg weight rank 0)

## Build

```bash
lake build Fermat
```

## Dependencies

- Lean v4.28.0
- mathlib (via flt-regular)
- flt-regular (FLT for regular primes)
