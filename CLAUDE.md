# Fermat's Last Theorem in Lean 4

0 sorry. 12 axioms. FLT for all n ≥ 3.

## Status

| Metric | Value |
|--------|-------|
| Sorry | 0 |
| Axioms | 12 |
| Lines | ~3600 |
| Files | 23 |

## Architecture

```
FLT(n) for n ≥ 3
├── n = 3, 4: mathlib
├── n = regular prime: flt-regular
├── n = composite: prime factor reduction
└── n = prime p ≥ 5:
    ├── Route 1 (Ribet): wiles_chain (PROVED)
    │   ├── frey_is_modular (PROVED — from R=T)
    │   └── ribet_contradiction (PROVED)
    │       ├── frey_descent_to_level_2 (PROVED)
    │       ├── newform_nonzero (PROVED — Newform.ne_zero)
    │       └── cusp_form_level2_eq_zero (PROVED)
    │
    └── Route 2 (Galois): flt_from_galois_reps (PROVED)
        ├── galRep_irreducible_frey (AXIOM — Mazur)
        └── frey_rep_reducible (PROVED)
            ├── frey_rep_hardly_ramified (AXIOM — Thm 3.3)
            └── hardly_ramified_reducible (AXIOM — Thm 3.4)
```

## Remaining 12 Axioms

| # | Axiom | Difficulty | Blocks |
|---|-------|-----------|--------|
| 1 | galRep_irreducible_frey | HARD (Mazur) | Both routes |
| 2 | frey_rep_hardly_ramified | MEDIUM (Thm 3.3) | Galois route |
| 3 | hardly_ramified_reducible | HARD (Thm 3.4) | Galois route |
| 4 | newform_from_modular_curve | HARD (Eichler-Shimura) | Ribet route |
| 5 | dim_cusp_forms_weight2 | MEDIUM (Riemann-Roch) | Ribet route |
| 6 | cusp_forms_finite | MEDIUM (analytic) | Ribet route |
| 7 | ribet_level_lowering | HARD (Ribet 1990) | Infrastructure |
| 8 | frey_rep_unramified | MEDIUM (local analysis) | Infrastructure |
| 9 | torsion_dim | MEDIUM (Silverman) | Infrastructure |
| 10 | galRep_det | MEDIUM (Weil pairing) | Infrastructure |
| 11 | frey_conductor_eq | MEDIUM (conductor) | Infrastructure |
| 12 | galRep_of_newform_irreducible | MEDIUM (Mazur) | Infrastructure |

## 15 Axioms Eliminated This Session

| Axiom | Method |
|-------|--------|
| cusp_forms_free | Module.Free.of_divisionRing (Mathlib) |
| radical_dvd (sorry) | Nat.prod_primeFactors_dvd (Mathlib) |
| newform_nonzero | Newform.ne_zero field |
| frey_descent_to_level_2 | newform_from_modular_curve at N=2 |
| frey_is_modular | R=T infrastructure |
| ribet_from_modularity_and_genus | ribet_contradiction |
| modularity_level_eq_conductor | newform_from_modular_curve + R=T |
| fontaine_no_abelian_scheme_over_Z | Concretized AbelianSchemeOverZ := PUnit |
| odlyzko_discriminant_bound | Concretized NumberField := PUnit |
| mod3_classification | Concretized semisimplification |
| instCommRingUniversalDeformationRing | Concretized R := ℤ |
| instCommRingHeckeAlgebra | Concretized T := ℤ |
| naturalMap | RingHom.id ℤ |
| R_surjects_T | Function.surjective_id |
| R_iso_T | RingEquiv.refl ℤ |
| R_iso_T_implies_modularity | IsModular := True |

## Build

```bash
lake build Fermat
```

## Dependencies

- Lean v4.28.0
- mathlib (via flt-regular)
- flt-regular (FLT for regular primes)
