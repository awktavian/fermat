/-
  Blueprint Alignment: Project Status & Imperial FLT Integration Map

  Last updated: 2026-03-01
  Project: ~/fermat — Top-down formalization of Fermat's Last Theorem in Lean 4

  ═══════════════════════════════════════════════════════════════════════════

  PROJECT SUMMARY

  11 Lean files, 810 lines. FLT for all n ≥ 3 proved modulo 3 axioms.

  Axioms (3):
    frey_semistable           Axioms.lean:52    Frey curve is semistable
    modularity_theorem        Axioms.lean:62    Semistable ⇒ modular (Wiles)
    ribet_from_modularity_and_genus Axioms.lean:84   Modular Frey + genus=0 ⇒ ⊥

  Opaques (2):
    IsSemistable              Axioms.lean:40    Semistability predicate
    IsModular                 Axioms.lean:44    Modularity predicate

  Sorries (1):
    sophie_germain            SophieGermain.lean:129   LTE descent (independent)

  ═══════════════════════════════════════════════════════════════════════════

  FILE MAP

  File                        Lines  Role
  ────────────────────────────────────────────────────────────────────────
  Basic.lean                   37    FermatLastTheorem, FLT_CaseI, flt_from_cases
  Descent/Infinite.lean        37    Generic descent (ℕ, ℤ)
  Cases/Five.lean              24    FLT(5) via flt-regular
  Cases/RegularPrimes.lean     49    FLT(regular primes), FLT(n∈[3,16])
  Cases/SophieGermain.lean    131    Case I for Sophie Germain primes [1 sorry]
  Modularity/FreyCurve.lean    66    Frey curve y²=x(x-aᵖ)(x+bᵖ), Δ≠0
  Modularity/GenusFormula.lean 165   genus(X₀(N)) for N=2..13, all by decide
  Modularity/NoCuspForms.lean  48    genus=0 ⇒ S₂(Γ₀(2))=0 (Riemann-Roch gap)
  Modularity/Axioms.lean      109    3 axioms + 2 opaques + wiles_chain
  Modularity/FLT.lean          68    flt_all_exponents: FLT for all n≥3
  Blueprint/Alignment.lean      —    This file (documentation only)

  ═══════════════════════════════════════════════════════════════════════════

  PROOF ARCHITECTURE

  The main theorem (FLT.lean:flt_all_exponents) for n ≥ 3 proceeds:
    n divisible by 4  → FLT(4) from mathlib (fermatLastTheoremFour)
    n has odd prime factor p ≥ 3:
      p = 3           → FLT(3) from mathlib (fermatLastTheoremThree)
      p ≥ 5           → wiles_chain (Axioms.lean)

  The Wiles chain composes three axioms:
    frey_semistable           : counterexample → semistable Frey curve
    modularity_theorem        : semistable → modular
    ribet_from_modularity_and_genus: modular Frey + genus=0 → ⊥ (genus proved, passed in)

  ═══════════════════════════════════════════════════════════════════════════

  PROVED RESULTS (no axioms, sorry-free)

  Result                             Source                   Method
  ─────────────────────────────────  ───────────────────────  ─────────────
  FLT(3)                             mathlib                  fermatLastTheoremThree
  FLT(4)                             mathlib                  fermatLastTheoremFour
  FLT(5)                             flt-regular              fermatLastTheoremFive
  FLT(7)                             flt-regular              fermatLastTheoremSeven
  FLT(11)                            flt-regular              fermatLastTheoremEleven
  FLT(13)                            flt-regular              fermatLastTheoremThirteen
  FLT(n) for 3 ≤ n ≤ 16             flt-regular              FLT_small
  FLT(regular primes)                flt-regular              flt_regular
  Frey curve Δ ≠ 0                   FreyCurve.lean           ring_nf + positivity
  Composite → prime reduction        FLT.lean                 Nat.minFac
  Case I / Case II splitting         Basic.lean               by_cases
  Infinite descent (ℕ, ℤ)            Descent/Infinite.lean    strongRecOn
  genus(X₀(N)) = 0 for N ∈ [2,10]   GenusFormula.lean        decide (kernel-verified)
  genus(X₀(11)) = 1                  GenusFormula.lean        decide
  Sophie Germain (partial)           SophieGermain.lean       1 sorry: LTE descent

  ═══════════════════════════════════════════════════════════════════════════

  AXIOM → IMPERIAL FLT BLUEPRINT MAPPING

  Imperial FLT: https://github.com/ImperialCollegeLondon/FLT
  Blueprint: https://imperialcollegelondon.github.io/FLT/blueprint/
  62 contributors, 1508 commits, funded through 2029.
  Status: building bottom-up (adeles, quaternion algebras, Hecke operators).
  Cannot yet state the modularity lifting theorem.

  Our Axiom                          Imperial Chapter(s)         Difficulty
  ─────────────────────────────────  ──────────────────────────  ──────────
  frey_semistable                    Ch 2 (First Reductions)     Medium
    Frey curve from FLT counter-     §2.1 Frey packages          Algebraic
    example is semistable.           §2.2 Frey curve              computation

  modularity_theorem                 Ch 4 (Proof Overview)       Extreme
    Semistable elliptic curves       Ch 6 (Modularity Lifting)   Multi-year
    over ℚ are modular.              Ch 5 (Automorphic Forms)    effort
                                     Ch 7 (Langlands)

  ribet_from_modularity_and_genus         Ch 3 (p-torsion)            Hard
    Modular Frey curve → ⊥.          §3.1 Reducibility            Requires
    Combines two sub-results:        +  S₂(Γ₀(2)) = 0            Galois rep
    (a) Ribet level-lowering              (genus proved,           theory
    (b) dim S₂(Γ₀(2)) = 0               Riemann-Roch gap)

  ═══════════════════════════════════════════════════════════════════════════

  AXIOM DECOMPOSITION DETAIL

  ribet_from_modularity_and_genus is a composite axiom encoding two facts:

  (a) Ribet's theorem (1990): modular Frey curve at level N has mod-p
      Galois representation arising from a weight-2 cusp form at level 2.
      This is the level-lowering step. Imperial: Chapter 3.

  (b) dim S₂(Γ₀(2)) = 0: there are no weight-2 cusp forms at level 2.
      The genus computation (genus X₀(2) = 0) is PROVED in GenusFormula.lean.
      The gap is the Riemann-Roch connection: genus = 0 ⇒ S₂ = 0.
      This is 19th century mathematics (Riemann 1857), not yet in mathlib.

  When mathlib has CuspForm with proper Γ₀ coercion, this axiom splits:
    ribet_theorem    : ∃ f : CuspForm (Γ₀(2)) 2, ρ̄_{E,p} ≅ ρ̄_{f,p}
    dim_S2_zero      : CuspForm (Γ₀(2)) 2 is trivial

  The second becomes provable once Riemann-Roch for algebraic curves
  is formalized. The genus computation itself is already kernel-verified.

  ═══════════════════════════════════════════════════════════════════════════

  KNOWN GAPS

  1. Sophie Germain sorry (SophieGermain.lean:129)
     LTE (Lifting the Exponent Lemma) descent on q-adic valuation.
     Independent: no other theorem depends on this. FLT(5) uses flt-regular.
     Estimated: ~200 lines of valuation theory.

  2. Riemann-Roch connection (NoCuspForms.lean)
     genus(X₀(2)) = 0 is proved. The link to dim S₂(Γ₀(2)) = 0 requires:
     • Algebraic curve structure on X₀(N)
     • Identification of S₂ with holomorphic differentials
     • Riemann-Roch for compact Riemann surfaces
     Currently absorbed into the ribet_from_modularity_and_genus axiom.

  3. IsSemistable / IsModular are opaque
     Full definitions require scheme-theoretic elliptic curve theory
     (Néron models, reduction types, modular forms as functions on the
     upper half-plane). These will come from Imperial's infrastructure.

  ═══════════════════════════════════════════════════════════════════════════

  STRATEGIC POSITION

  Imperial builds bottom-up: adeles → automorphic forms → modularity lifting.
  We build top-down: FLT → Wiles chain → precisely decomposed axioms.

  Advantage: our proof skeleton is complete. When Imperial proves a theorem,
  replacement is mechanical:
    1. Add `import FLT.Chapter.Theorem`
    2. Replace our axiom with proof invoking their theorem
    3. `lake build` to verify compatibility
    4. Delete the axiom declaration

  Priority for axiom replacement (most likely first):
    1. frey_semistable — algebraic, bounded scope, Ch 2 is active
    2. ribet_from_modularity_and_genus — 1990 mathematics, well-understood
       (further accelerated if Riemann-Roch enters mathlib, splitting the axiom)
    3. modularity_theorem — deepest, will be last (Wiles 1995, BCDT 2001)
       Imperial cannot yet state this; Chapters 4-7 are years of work

  ═══════════════════════════════════════════════════════════════════════════

  DEPENDENCIES

  External Lean packages:
    mathlib       — FLT(3), FLT(4), WeierstrassCurve, ZMod, core algebra
    flt-regular   — FLT(regular primes), FLT(5,7,11,13), FLT_small

  ═══════════════════════════════════════════════════════════════════════════
-/

-- This file is documentation only. No Lean declarations.
-- Axioms: Fermat.Modularity.Axioms
-- Main theorem: Fermat.Modularity.FLT.flt_all_exponents
-- Genus proof: Fermat.Modularity.GenusFormula.genus_X0_2_eq_zero
