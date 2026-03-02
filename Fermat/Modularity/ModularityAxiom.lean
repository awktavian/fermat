/-
  Precise Modularity Axiom (WP7)

  Replaces the opaque `IsModular` predicate and the coarse `frey_is_modular`
  axiom (Axioms.lean) with a precisely typed statement that uses the actual
  Galois representation types from WP2–WP4:

    ∃ N, ∃ f : Newform N 2, ρ̄_{f,p} = ρ̄_{E,p}

  This is the Taniyama–Shimura–Wiles modularity theorem specialized to the
  Frey curve: every semistable elliptic curve over ℚ is modular, meaning
  its mod-p Galois representation arises from a weight-2 newform via the
  Eichler–Shimura construction.

  The axiom `modularity_level_eq_conductor` is the strongest form: the
  witnessing newform lives at level equal to the Artin conductor of the
  Frey curve's Galois representation. The theorem `modularity_of_frey`
  is derived from it, providing the existential `IsModularPrecise` statement.

  Imperial FLT Blueprint: Chapters 4, 6 (Modularity Lifting Theorems).
-/

import Fermat.ModularForms.Newform
import Fermat.GaloisRep.Conductor

namespace Fermat

open Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Precise Modularity Predicate
-- ═══════════════════════════════════════════════════════════════════════════

/-- An elliptic curve E/ℚ is modular at prime p (in the precise sense) if
there exists a level N and a weight-2 newform f at that level whose mod-p
Galois representation equals that of E:

  ∃ N, ∃ f : Newform N 2, ρ̄_{f,p} = ρ̄_{E,p}

This replaces the opaque `IsModular` from Axioms.lean with a statement
that threads through the actual `GaloisRep 2 (ZMod p) ℚ` types defined
in WP2 (galRepOfCurve) and WP4 (galRepOfNewform).

The equality is on `GaloisRep 2 (ZMod p) ℚ`, which is equality of group
homomorphisms Gal(Q̄/Q) →* GL₂(𝔽ₚ). This is isomorphism of the
underlying representations (same traces at all Frobenius elements). -/
def IsModularPrecise (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ N : ℕ, ∃ f : Newform N 2, galRepOfNewform f p = galRepOfCurve E p

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Modularity at the Conductor Level (Thin Axiom)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Wiles, 1995; Taylor–Wiles).** The Frey curve attached to a
putative FLT counterexample a^p + b^p = c^p is modular, and the witnessing
newform lives at level equal to the Artin conductor of the Frey curve's
mod-p Galois representation.

This is the strongest form of the modularity axiom: it simultaneously
asserts existence of a matching newform AND pins the level to the
conductor. The weaker existential `IsModularPrecise` follows as a
corollary (§3).

This replaces both `frey_is_modular` and the opaque `IsModular` from
Axioms.lean. The improvement: `IsModular` was an opaque `Prop` with no
internal structure. Here, the statement is fully typed — the newform f,
the Galois representations `galRepOfNewform f p` and `galRepOfCurve E p`,
and their equality all live in the concrete types from WP2–WP4.

Imperial FLT Blueprint: Chapters 4, 6. -/
axiom modularity_level_eq_conductor (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ f : Newform (conductorOf p (galRepOfCurve (freyCurve a b p) p)) 2,
      galRepOfNewform f p = galRepOfCurve (freyCurve a b p) p

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Modularity of the Frey Curve (Derived)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Frey curve is modular in the precise sense: there exists a weight-2
newform whose mod-p Galois representation matches the Frey curve's.

Derived from `modularity_level_eq_conductor` by existential introduction
with N = conductor. This is the direct replacement for the old
`frey_is_modular` axiom, now a theorem rather than an axiom. -/
theorem modularity_of_frey (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsModularPrecise (freyCurve a b p) p :=
  ⟨conductorOf p (galRepOfCurve (freyCurve a b p) p),
   modularity_level_eq_conductor a b c p hp5 heq ha hb hc⟩

end Fermat
