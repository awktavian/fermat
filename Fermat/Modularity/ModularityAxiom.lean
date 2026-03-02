/-
  Precise Modularity — Conductor-Level Newform Existence

  Provides the precise modularity statement: the Frey curve's mod-p
  Galois representation arises from a weight-2 newform at the conductor level.

  Previously axiomatized as `modularity_level_eq_conductor`. Now derived
  from `newform_from_modular_curve` (which provides a matching newform at
  any level) composed with the modularity proof from R=T infrastructure.

  Imperial FLT Blueprint: Chapters 4, 6 (Modularity Lifting Theorems).
-/

import Fermat.ModularForms.Newform
import Fermat.GaloisRep.Conductor
import Fermat.Modularity.DeformationRing

namespace Fermat

open Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Precise Modularity Predicate
-- ═══════════════════════════════════════════════════════════════════════════

/-- An elliptic curve E/ℚ is modular at prime p (in the precise sense) if
there exists a level N and a weight-2 newform f at that level whose mod-p
Galois representation equals that of E. -/
def IsModularPrecise (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ N : ℕ, ∃ f : Newform N 2, galRepOfNewform f p = galRepOfCurve E p

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Modularity at the Conductor Level (Derived)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (was axiom).** The Frey curve's mod-p Galois representation
arises from a weight-2 newform at the conductor level.

Derived from:
1. `frey_modular_from_R_eq_T`: R=T infrastructure gives `IsModular`
2. `newform_from_modular_curve`: modularity gives a matching newform at any level
3. Instantiated at level = conductor

Previously axiomatized as `modularity_level_eq_conductor`. -/
theorem modularity_level_eq_conductor (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ f : Newform (conductorOf p (galRepOfCurve (freyCurve a b p) p)) 2,
      galRepOfNewform f p = galRepOfCurve (freyCurve a b p) p :=
  let hmod := (frey_modular_from_R_eq_T a b p hp5
    (galRepOfCurve (freyCurve a b p) p)
    (galRep_irreducible_frey a b c p hp5 heq ha hb hc)) 0
  newform_from_modular_curve (freyCurve a b p)
    (conductorOf p (galRepOfCurve (freyCurve a b p) p)) hmod p

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Modularity of the Frey Curve (Derived)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Frey curve is modular in the precise sense. -/
theorem modularity_of_frey (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsModularPrecise (freyCurve a b p) p :=
  ⟨conductorOf p (galRepOfCurve (freyCurve a b p) p),
   modularity_level_eq_conductor a b c p hp5 heq ha hb hc⟩

end Fermat
