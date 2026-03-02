# Fermat's Last Theorem in Lean 4

0 sorry. 2 axioms. FLT for all n ≥ 3.

## Status

| Metric | Value |
|--------|-------|
| Sorry | 0 |
| Axioms | 2 (frey_is_modular, ribet_from_modularity_and_genus) |
| Lines | ~1750 |
| Files | 12 |

## Architecture

```
FLT(n) for n ≥ 3
├── n = 3, 4: mathlib
├── n = regular prime: flt-regular
├── n = composite: prime factor reduction
└── n = prime p ≥ 5: wiles_chain
    ├── frey_is_modular (AXIOM — Wiles 1995 + semistability at ℓ=2)
    └── ribet_from_modularity_and_genus (AXIOM — Ribet 1990 + Riemann-Roch)
        └── genus(X₀(2)) = 0 (PROVED — kernel-verified by decide)
```

## Proved Results (sorry-free)

- Sophie Germain's theorem (Case I for SG primes) — coprime factorization + ZMod
- Frey curve Δ ≠ 0
- Frey semistability at odd primes (IsSemistableInt)
- genus(X₀(N)) for N = 2..13
- FLT for regular primes, n ∈ [3,16]

## Contributing via Agents

8 work packages (WP1-WP8) build the infrastructure to decompose the 2 monolithic axioms into thin, precisely-typed axioms. Each WP produces a self-contained Lean file.

### Wave 1 (no dependencies)
- **WP1**: Continuous Galois representations (`Fermat/GaloisRep/Basic.lean`)
- **WP5**: Riemann-Roch genus connection (`Fermat/ModularForms/RiemannRoch.lean`)

### Wave 2 (depends on WP1)
- **WP2**: Galois rep from elliptic curves (`Fermat/GaloisRep/EllipticCurve.lean`)
- **WP3**: Conductor and ramification (`Fermat/GaloisRep/Conductor.lean`)

### Wave 3 (depends on WP1-3)
- **WP4**: Hecke eigenforms and newforms (`Fermat/ModularForms/Newform.lean`)

### Wave 4 (depends on WP1-5)
- **WP6**: Ribet's theorem statement (`Fermat/Modularity/Ribet.lean`)
- **WP7**: Modularity theorem statement (`Fermat/Modularity/ModularityAxiom.lean`)

### Wave 5 (depends on all)
- **WP8**: Integration — rewrite wiles_chain with proper types

### To contribute:
1. Pick an unclaimed WP
2. Branch: `git checkout -b wp{N}-{description}`
3. Implement the Lean file
4. `lake build Fermat` must pass
5. Submit PR

## Build

```bash
lake build Fermat
```

## Dependencies

- Lean v4.28.0
- mathlib (via flt-regular)
- flt-regular (FLT for regular primes)
