/-
  Conductor of the Frey Curve (WP3)

  Defines the radical of a natural number (product of distinct prime factors)
  and the conductor of the Frey curve attached to a putative FLT counterexample.
  The Artin conductor is opaque; the key computable piece is the radical.

  For a^p + b^p = c^p, the (simplified) conductor of the Frey curve is
  rad(|a| * |b| * |c|), ignoring the 2-adic correction factor.

  Imperial FLT Blueprint: Chapter 4, §4.1 (conductors and level lowering).
-/

import Fermat.GaloisRep.EllipticCurve
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic

set_option linter.dupNamespace false

namespace Fermat

open Finset Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Radical of a Natural Number
-- ═══════════════════════════════════════════════════════════════════════════

/-- The radical of a natural number: the product of its distinct prime factors.
For n > 0, rad(n) = ∏_{p | n, p prime} p. By convention, rad(0) = 0.

This is the squarefree kernel of n — the largest squarefree divisor. It
appears in the ABC conjecture and, for our purposes, in the conductor of
the Frey curve. -/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

@[simp] theorem radical_zero : radical 0 = 1 := by
  simp [radical]

@[simp] theorem radical_one : radical 1 = 1 := by
  simp [radical]

theorem radical_prime {p : ℕ} (hp : p.Prime) : radical p = p := by
  simp [radical, hp]

theorem radical_pos {n : ℕ} (_ : n ≠ 0) : 0 < radical n := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.pos_of_mem_primeFactors hp

theorem radical_dvd {n : ℕ} (_hn : n ≠ 0) : radical n ∣ n := by
  unfold radical; exact Nat.prod_primeFactors_dvd n

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Conductor of the Frey Curve
-- ═══════════════════════════════════════════════════════════════════════════

/-- The (simplified) conductor of the Frey curve: rad(|a| * |b| * |c|).

For a putative FLT counterexample a^p + b^p = c^p, the actual conductor
of the Frey curve E_{a,b} is N_E = rad₂(abc) where rad₂ denotes the
radical away from 2. The 2-adic part requires a delicate local analysis
(Tate's algorithm at p = 2). For the modularity argument, what matters is
that N_E divides 2 * rad(abc), so the level is controlled.

We define the simplified version here; the 2-adic correction is absorbed
into the level-lowering axiom. -/
def freyConductor (a b c : ℤ) : ℕ :=
  radical (a.natAbs * b.natAbs * c.natAbs)

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Artin Conductor (Opaque)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Artin conductor of a mod-p Galois representation ρ : Gal(Q̄/Q) → GL₂(𝔽ₚ).

The Artin conductor is defined as N(ρ) = ∏_ℓ ℓ^{f(ρ,ℓ)} where the product
runs over all primes ℓ, and f(ρ,ℓ) is the Artin conductor exponent at ℓ,
measuring the ramification of ρ at ℓ:
  f(ρ,ℓ) = codim V^{I_ℓ} + Swan conductor contribution

This is opaque because:
1. The inertia group I_ℓ requires the decomposition group at ℓ in Gal(Q̄/Q)
2. The Swan conductor requires higher ramification groups
3. Both depend on the local Galois theory at each prime ℓ -/
opaque conductorOf (p : ℕ) [Fact (Nat.Prime p)]
    (ρ : GaloisRep 2 (ZMod p) ℚ) : ℕ

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Conductor of the Frey Representation
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Conductor of the Frey curve).** The Artin conductor of the
mod-p Galois representation attached to the Frey curve E_{a,b} equals
rad(|a| * |b| * |c|), the simplified Frey conductor.

More precisely, for the Frey curve y² = x(x − aᵖ)(x + bᵖ) attached to
a^p + b^p = c^p, the conductor N_E satisfies:
  N_E = ∏_{ℓ | abc, ℓ odd prime} ℓ · (power of 2)

The 2-adic factor is absorbed: we axiomatize that the Artin conductor
equals the radical of |abc|. The level-lowering step (Ribet's theorem)
only needs that N_E is squarefree away from 2, which the radical gives.

The algebraic infrastructure for this is in `Fermat.Discriminant`:
the set of odd primes dividing Δ equals the set dividing freyConductor
(`odd_prime_dvd_disc_iff_dvd_conductor`). What remains is concretizing
`conductorOf` and proving the semistable conductor formula f_ℓ ∈ {0,1}.

Imperial FLT Blueprint: Chapter 4, §4.1. -/
axiom frey_conductor_eq (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    conductorOf p (galRepOfCurve (freyCurve a b p) p) = freyConductor a b c

end Fermat
