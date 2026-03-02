# Fermat's Last Theorem in Lean 4

0 sorry. 25 axioms. FLT for all n ≥ 3.

## Status

| Metric | Value |
|--------|-------|
| Sorry | 0 |
| Axioms | 25 (decomposed across 2 proof routes) |
| Lines | ~3650 |
| Files | 23 |

## Architecture

Two independent proof routes for primes p ≥ 5, plus direct computation for small cases.

```
FLT(n) for n ≥ 3
├── n = 3, 4: mathlib
├── n = regular prime: flt-regular
├── n = composite: prime factor reduction
└── n = prime p ≥ 5:
    ├── Route 1 (Ribet): wiles_chain
    │   ├── frey_is_modular (AXIOM — Wiles 1995)
    │   └── ribet_from_modularity_and_genus (AXIOM — Ribet 1990)
    │       └── genus(X₀(2)) = 0 (PROVED — by decide)
    │
    └── Route 2 (Galois): flt_from_galois_reps (PROVED)
        ├── galRep_irreducible_frey (AXIOM — Mazur 1978)
        └── frey_rep_reducible (PROVED)
            ├── frey_rep_hardly_ramified (AXIOM — Thm 3.3)
            └── hardly_ramified_reducible (AXIOM — Thm 3.4)
```

Route 1 is further decomposed via `ribet_contradiction` (PROVED):
```
ribet_contradiction (PROVED)
├── frey_descent_to_level_2 (AXIOM)
├── newform_nonzero (PROVED — from Newform.ne_zero)
└── cusp_form_level2_eq_zero (PROVED)
    ├── dim_cusp_forms_weight2 (AXIOM — Riemann-Roch)
    ├── cusp_forms_finite (AXIOM)
    ├── cusp_forms_free (PROVED — Module.Free.of_divisionRing)
    └── genus_zero_of_2 (PROVED — by decide)
```

## Proved Results (sorry-free)

- Sophie Germain's theorem (Case I for SG primes) — 760 lines, coprime factorization + ZMod
- Frey curve Δ ≠ 0
- Frey semistability at odd primes (IsSemistableInt)
- genus(X₀(N)) for N = 2..13 (by decide)
- cusp_form_level2_eq_zero — every f ∈ S₂(Γ₀(2)) is zero
- ribet_contradiction — level descent + no cusp forms at level 2 = ⊥
- flt_from_galois_reps — Mazur (irreducible) vs Serre (reducible) = ⊥
- cusp_forms_free — Module.Free.of_divisionRing (was axiom)
- newform_nonzero — from Newform.ne_zero field (was axiom)
- radical_dvd — Nat.prod_primeFactors_dvd (was sorry)
- FLT for regular primes, n ∈ [3,16]

## Axiom Budget (25)

| Category | Count | Axioms |
|----------|-------|--------|
| Modularity (Wiles) | 2 | frey_is_modular, ribet_from_modularity_and_genus |
| Ribet chain | 3 | ribet_level_lowering, frey_rep_unramified, frey_descent_to_level_2 |
| Galois reps | 3 | galRep_irreducible_frey, frey_rep_hardly_ramified, hardly_ramified_reducible |
| Riemann-Roch | 2 | dim_cusp_forms_weight2, cusp_forms_finite |
| R=T infrastructure | 6 | CommRing R, CommRing T, naturalMap, R_surjects_T, R_iso_T, R_iso_T_implies_modularity |
| Precise modularity | 1 | modularity_level_eq_conductor |
| EC infrastructure | 3 | torsion_dim, galRep_det, frey_conductor_eq |
| Newform infrastructure | 2 | newform_from_modular_curve, galRep_of_newform_irreducible |
| Mod 3 | 3 | fontaine_no_abelian_scheme_over_Z, odlyzko_discriminant_bound, mod3_classification |

## Contributing

### To eliminate an axiom:
1. Prove the corresponding theorem in Lean against Mathlib
2. Import it in the fermat repo
3. Replace `axiom foo ...` with `theorem foo ... := <proof>`
4. `lake build Fermat` — verify 0 errors
5. The axiom count decreases by 1

### Recommended attack order (highest impact first):
1. **dim_cusp_forms_weight2** — Riemann-Roch for modular curves. ~500 lines.
2. **frey_rep_hardly_ramified** (Thm 3.3) — verify 4 conditions on Frey curve. ~1000 lines.
3. **mod3_classification** (Thm 3.9) — classify hardly ramified mod 3 reps. ~1500 lines.
4. **hardly_ramified_reducible** (Thm 3.4) — compose Thms 3.6+3.7+3.9. HARD.
5. **R_iso_T** — Taylor-Wiles patching. EXTREME.

## Build

```bash
lake build Fermat
```

## Dependencies

- Lean v4.28.0
- mathlib (via flt-regular)
- flt-regular (FLT for regular primes)
