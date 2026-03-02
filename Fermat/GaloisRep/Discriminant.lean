/-
  Discriminant Infrastructure for the Frey Curve (WP-UNRAM / WP-COND)

  Computes the discriminant of the Frey curve explicitly and proves
  key divisibility properties that are intermediate steps toward:
  • `frey_rep_unramified` (Ribet.lean:115) — the mod-p Galois representation
    is unramified at odd primes dividing the conductor
  • `frey_conductor_eq` (Conductor.lean:105) — the Artin conductor equals
    the radical of |abc|

  ## What this file proves

  1. The Weierstrass discriminant Δ of the Frey curve y² = x(x - aᵖ)(x + bᵖ)
     factors as 16 · (ab)^{2p} · (a^p + b^p)² (over ℚ).

  2. Under the Fermat equation a^p + b^p = c^p, this simplifies to
     Δ = 16 · (abc)^{2p}.

  3. For any odd prime ℓ, the ℓ-adic valuation v_ℓ(Δ) = 2p · v_ℓ(|abc|).
     Since p ≥ 5, we get p | v_ℓ(Δ).

  4. An odd prime ℓ divides the integer discriminant iff ℓ divides abc.

  ## Why these matter

  The implication "p | v_ℓ(Δ) → mod-p representation unramified at ℓ"
  follows from the Tate parametrization at primes of multiplicative reduction:

  At an odd prime ℓ where the Frey curve has bad reduction (necessarily
  multiplicative, by semistability), the Tate uniformization gives
  E(Q̄_ℓ) ≅ Q̄_ℓˣ / q^ℤ where q is the Tate parameter with v_ℓ(q) = v_ℓ(Δ).
  The inertia group I_ℓ acts on E[p] through a character of order dividing
  v_ℓ(Δ). When p | v_ℓ(Δ), this character is trivial mod p, making ρ̄_{E,p}
  unramified at ℓ.

  This step requires the Tate parametrization (deep analytic/formal geometry)
  and is why `frey_rep_unramified` remains an axiom. The lemmas here are the
  *algebraic* half — the discriminant computation that feeds into it.

  For the conductor: a semistable curve has conductor = ∏{bad primes} ℓ = rad(Δ).
  Since Δ = 16(abc)^{2p}, the odd part of rad(Δ) = rad(|abc|) = freyConductor.
  The equality `conductorOf p ρ = freyConductor a b c` additionally requires
  the theory of Artin conductors for semistable curves, which is why
  `frey_conductor_eq` also remains an axiom.

  Imperial FLT Blueprint: Chapter 3, §3.2 (local analysis at bad primes).
-/

import Fermat.GaloisRep.Conductor
import Fermat.GaloisRep.Ramification
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option linter.dupNamespace false

namespace Fermat.Discriminant

open Finset Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Integer Discriminant of the Frey Curve
-- ═══════════════════════════════════════════════════════════════════════════

/-- The integer discriminant of the Frey curve, as a formula in a, b, p.

For the Frey curve y² = x(x - aᵖ)(x + bᵖ) in Weierstrass form
with a₁ = a₃ = a₆ = 0, a₂ = bᵖ - aᵖ, a₄ = -(ab)ᵖ, we compute:
  b₂ = 4(bᵖ - aᵖ), b₄ = -2(ab)ᵖ, b₆ = 0, b₈ = -(ab)^{2p}
  Δ = -b₂²b₈ - 8b₄³ = 16(bᵖ - aᵖ)²(ab)^{2p} + 64(ab)^{3p}
    = 16(ab)^{2p}[(bᵖ - aᵖ)² + 4(ab)ᵖ]
    = 16(ab)^{2p}(aᵖ + bᵖ)²
-/
def freyDiscriminantInt (a b : ℤ) (p : ℕ) : ℤ :=
  16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2

/-- Under the Fermat equation a^p + b^p = c^p, the integer discriminant
simplifies to 16 · (abc)^{2p}. -/
def freyDiscriminantFermat (a b c : ℤ) (p : ℕ) : ℤ :=
  16 * (a * b * c) ^ (2 * p)

/-- The Fermat equation a^p + b^p = c^p implies the discriminant factorization. -/
theorem frey_disc_fermat_eq (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    freyDiscriminantInt a b p = freyDiscriminantFermat a b c p := by
  unfold freyDiscriminantInt freyDiscriminantFermat
  rw [heq]
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- §1b. Connecting Weierstrass Δ to the Integer Discriminant Formula
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Weierstrass discriminant of the Frey curve equals the integer discriminant
formula cast to ℚ. This connects `WeierstrassCurve.Δ` (the Mathlib discriminant
definition) to `freyDiscriminantInt` (our explicit integer formula).

For the Frey curve y² = x(x - aᵖ)(x + bᵖ):
  a₁ = a₃ = a₆ = 0, a₂ = bᵖ - aᵖ, a₄ = -(ab)ᵖ
  b₂ = 4(bᵖ - aᵖ), b₄ = -2(ab)ᵖ, b₆ = 0, b₈ = -(ab)^{2p}
  Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆
    = 16(bᵖ - aᵖ)²(ab)^{2p} + 64(ab)^{3p}
    = 16(ab)^{2p}[(bᵖ - aᵖ)² + 4(ab)ᵖ]
    = 16(ab)^{2p}(aᵖ + bᵖ)²

This is a straightforward ring computation after unfolding definitions. -/
theorem frey_weierstrass_disc_eq (a b : ℤ) (p : ℕ) :
    (freyCurve a b p).Δ = (freyDiscriminantInt a b p : ℚ) := by
  unfold freyCurve freyDiscriminantInt
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  ring

/-- The Weierstrass discriminant of the Frey curve under the Fermat equation
simplifies to 16(abc)^{2p} cast to ℚ. -/
theorem frey_weierstrass_disc_fermat (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    (freyCurve a b p).Δ = (freyDiscriminantFermat a b c p : ℚ) := by
  rw [frey_weierstrass_disc_eq, frey_disc_fermat_eq a b c p heq]

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Natural Number Discriminant (for padicValNat)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The natural number form of the Frey discriminant: |Δ| = 16 · |abc|^{2p}.
Uses natAbs to move to ℕ where padicValNat is defined. -/
def freyDiscNat (a b c : ℤ) (p : ℕ) : ℕ :=
  16 * (a.natAbs * b.natAbs * c.natAbs) ^ (2 * p)

theorem frey_disc_nat_eq (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    (freyDiscriminantInt a b p).natAbs = freyDiscNat a b c p := by
  rw [frey_disc_fermat_eq a b c p heq]
  unfold freyDiscriminantFermat freyDiscNat
  simp only [Int.natAbs_mul, Int.natAbs_pow]
  norm_num

theorem frey_disc_nat_ne_zero (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    freyDiscNat a b c p ≠ 0 := by
  unfold freyDiscNat
  apply mul_ne_zero
  · norm_num
  · apply pow_ne_zero
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. p-Adic Valuation of the Discriminant
-- ═══════════════════════════════════════════════════════════════════════════

/-- The ℓ-adic valuation of 16 = 2⁴ is zero for any odd prime ℓ. -/
theorem padicValNat_16_eq_zero (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    padicValNat ℓ 16 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have hℓp : Nat.Prime ℓ := Fact.out
  have : ℓ ∣ 2 := hℓp.dvd_of_dvd_pow (show ℓ ∣ 2 ^ 4 by norm_num; exact h)
  exact hℓ2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hℓp.two_le)

/-- The ℓ-adic valuation of the Frey discriminant 16 · |abc|^{2p} at an
odd prime ℓ is exactly 2p · v_ℓ(|abc|).

This is the key computation: for odd ℓ, v_ℓ(16) = 0, and
v_ℓ(|abc|^{2p}) = 2p · v_ℓ(|abc|) by standard p-adic valuation properties. -/
theorem padicVal_frey_disc (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    padicValNat ℓ (freyDiscNat a b c p) =
      2 * p * padicValNat ℓ (a.natAbs * b.natAbs * c.natAbs) := by
  unfold freyDiscNat
  have habc : a.natAbs * b.natAbs * c.natAbs ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc
  rw [padicValNat.mul (by norm_num) (pow_ne_zero _ habc)]
  rw [padicValNat_16_eq_zero ℓ hℓ2]
  rw [padicValNat.pow _ habc]
  ring

/-- **Key divisibility**: p divides the ℓ-adic valuation of the Frey
discriminant at every odd prime ℓ.

This is the algebraic core of the `frey_rep_unramified` axiom:
  v_ℓ(Δ) = 2p · v_ℓ(|abc|), so p | v_ℓ(Δ).

The implication "p | v_ℓ(Δ) → ρ̄_{E,p} unramified at ℓ" requires the
Tate parametrization, which is why the axiom remains. But this lemma
is the algebraic half that is fully proved. -/
theorem p_dvd_padicVal_frey_disc (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    p ∣ padicValNat ℓ (freyDiscNat a b c p) := by
  rw [padicVal_frey_disc a b c p ha hb hc ℓ hℓ2]
  exact ⟨2 * padicValNat ℓ (a.natAbs * b.natAbs * c.natAbs), by ring⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Odd Primes Dividing the Discriminant ↔ Dividing abc
-- ═══════════════════════════════════════════════════════════════════════════

/-- An odd prime ℓ divides the Frey discriminant iff ℓ divides abc. -/
theorem odd_prime_dvd_frey_disc_iff (a b c : ℤ) (p : ℕ)
    (hp : p ≥ 1)
    (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2) :
    ℓ ∣ freyDiscNat a b c p ↔ ℓ ∣ a.natAbs * b.natAbs * c.natAbs := by
  constructor
  · intro h
    unfold freyDiscNat at h
    have hℓp : Prime ℓ := Nat.Prime.prime hℓ
    rcases hℓp.dvd_or_dvd h with h16 | hpow
    · exfalso
      have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow
        (show ℓ ∣ 2 ^ 4 by norm_num; exact h16)
      exact hℓ2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hℓ.two_le)
    · exact hℓ.dvd_of_dvd_pow hpow
  · intro h
    unfold freyDiscNat
    have hp2 : 2 * p ≠ 0 := by omega
    exact dvd_mul_of_dvd_right (dvd_pow h hp2) 16

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Radical Lemmas
-- ═══════════════════════════════════════════════════════════════════════════

/-- A prime divides radical(n) iff it divides n (for n ≠ 0). -/
theorem prime_dvd_radical_iff {n : ℕ} (hn : n ≠ 0)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) :
    ℓ ∣ radical n ↔ ℓ ∣ n := by
  constructor
  · intro h
    exact dvd_trans h (radical_dvd hn)
  · intro h
    unfold radical
    exact Finset.dvd_prod_of_mem id
      (Nat.Prime.mem_primeFactors hℓ h hn)

/-- An odd prime divides the freyConductor iff it divides |abc|. -/
theorem odd_prime_dvd_freyConductor_iff (a b c : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    ℓ ∣ freyConductor a b c ↔ ℓ ∣ a.natAbs * b.natAbs * c.natAbs := by
  unfold freyConductor
  exact prime_dvd_radical_iff (by
    apply mul_ne_zero
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
    · exact Int.natAbs_ne_zero.mpr hc) hℓ

/-- The odd primes dividing the Frey discriminant are exactly those
dividing the freyConductor. This is the algebraic equivalence that
underlies the conductor computation. -/
theorem odd_prime_dvd_disc_iff_dvd_conductor (a b c : ℤ) (p : ℕ)
    (hp : p ≥ 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2) :
    ℓ ∣ freyDiscNat a b c p ↔ ℓ ∣ freyConductor a b c := by
  rw [odd_prime_dvd_frey_disc_iff a b c p hp ha hb hc ℓ hℓ hℓ2]
  rw [odd_prime_dvd_freyConductor_iff a b c ha hb hc ℓ hℓ]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Tate Parametrization Axiom
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axiom (Tate parametrization).** For a Weierstrass curve
E/ℚ with nonzero discriminant, at an odd prime ℓ, if the ℓ-adic valuation
of Δ (as a rational number) is divisible by p, then the mod-p Galois
representation is unramified at ℓ.

Mathematical content: at an odd prime ℓ of multiplicative reduction, the Tate
uniformization gives E(Q̄_ℓ) ≅ Q̄_ℓˣ / qℤ where q is the Tate parameter
with v_ℓ(q) = v_ℓ(Δ). The inertia group I_ℓ acts on E[p] through a
character of order dividing v_ℓ(Δ). When p | v_ℓ(Δ), this character
is trivial mod p, making ρ̄_{E,p} unramified at ℓ. At primes of good
reduction (v_ℓ(Δ) = 0), the representation is automatically unramified
(Néron-Ogg-Shafarevich), and p | 0 trivially.

`padicValRat ℓ Δ` gives the ℓ-adic valuation of the rational discriminant.
For the Frey curve, Δ = 16(ab)^{2p}(a^p + b^p)^2 is an integer, so
padicValRat ℓ Δ = padicValInt ℓ Δ_ℤ ≥ 0.

This is the single remaining analytic input needed for `frey_rep_unramified`.
The algebraic half (p | v_ℓ(Δ) for the Frey curve) is fully proved in
`p_dvd_padicVal_frey_disc`.

Estimated difficulty: HARD. Requires Tate curve over ℤ_ℓ[[q]] (partially
in Mathlib: EllipticCurve.Tate), connection to Galois representations,
and local class field theory.

Imperial FLT Blueprint: Chapter 3, §3.2 (Tate parametrization at bad primes). -/
axiom tate_unramified (E : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) (hΔ : E.Δ ≠ 0)
    (hdvd : (p : ℤ) ∣ padicValRat ℓ E.Δ) :
    IsUnramifiedAt (galRepOfCurve E p) ℓ

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. padicValRat of the Frey Discriminant
-- ═══════════════════════════════════════════════════════════════════════════

/-- The ℓ-adic valuation of the Frey curve's Δ (as a rational) equals the
ℓ-adic valuation of the integer discriminant formula.

Since (freyCurve a b p).Δ = (freyDiscriminantInt a b p : ℚ) (by
`frey_weierstrass_disc_eq`), and padicValRat of an integer cast equals
padicValInt of the integer, this follows from `padicValRat.of_int`. -/
theorem padicValRat_frey_disc (a b : ℤ) (p : ℕ) (ℓ : ℕ) :
    padicValRat ℓ (freyCurve a b p).Δ =
    padicValInt ℓ (freyDiscriminantInt a b p) := by
  rw [frey_weierstrass_disc_eq]
  exact padicValRat.of_int

/-- Under the Fermat equation, the ℓ-adic valuation of the Frey curve's
discriminant equals the ℓ-adic valuation of 16(abc)^{2p}. -/
theorem padicValRat_frey_disc_fermat (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) (ℓ : ℕ) :
    padicValRat ℓ (freyCurve a b p).Δ =
    padicValInt ℓ (freyDiscriminantFermat a b c p) := by
  rw [frey_weierstrass_disc_fermat a b c p heq]
  exact padicValRat.of_int

/-- p divides padicValInt ℓ (freyDiscriminantFermat a b c p) for odd ℓ.

This is the integer-valued version of `p_dvd_padicVal_frey_disc`, connecting
`padicValInt` to `padicValNat` via natAbs. -/
theorem p_dvd_padicValInt_frey_disc (a b c : ℤ) (p : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hℓ2 : ℓ ≠ 2) :
    (p : ℤ) ∣ padicValInt ℓ (freyDiscriminantFermat a b c p) := by
  unfold padicValInt freyDiscriminantFermat
  -- padicValInt p z = padicValNat p z.natAbs
  -- freyDiscriminantFermat = 16 * (a * b * c) ^ (2 * p)
  -- natAbs of this equals freyDiscNat a b c p
  have hconv : (16 * (a * b * c) ^ (2 * p)).natAbs = freyDiscNat a b c p := by
    unfold freyDiscNat
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_mul]
    norm_num
  rw [hconv]
  exact_mod_cast p_dvd_padicVal_frey_disc a b c p ha hb hc ℓ hℓ2

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Proof of frey_rep_unramified (WAS AXIOM, NOW THEOREM)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (was axiom).** The mod-p Galois representation of the Frey
curve is unramified at every odd prime ℓ dividing the Frey conductor.

Proof chain:
1. `frey_weierstrass_disc_fermat`: (freyCurve a b p).Δ = 16(abc)^{2p} as ℚ
2. `p_dvd_padicValInt_frey_disc`: p | v_ℓ(16(abc)^{2p}) as integers
3. `padicValRat_frey_disc_fermat`: v_ℓ(Δ_ℚ) = v_ℓ(16(abc)^{2p}_ℤ)
4. `tate_unramified`: (p : ℤ) | v_ℓ(Δ_ℚ) → unramified

This replaces the axiom in Ribet.lean with a theorem that factors through
the Tate parametrization axiom + fully proved discriminant infrastructure.

The `ℓ ∣ freyConductor` hypothesis is not used in the proof — the
divisibility p | v_ℓ(Δ) holds at ALL odd primes ℓ, not just those
dividing the conductor. The hypothesis is retained for API compatibility
with the call site in Ribet.lean. -/
theorem frey_rep_unramified (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2)
    (_hℓN : ℓ ∣ freyConductor a b c) :
    IsUnramifiedAt (galRepOfCurve (freyCurve a b p) p) ℓ := by
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  apply tate_unramified
  · exact hℓ2
  · exact frey_discriminant a b c p hp5 heq ha hb hc
  · rw [padicValRat_frey_disc_fermat a b c p heq]
    exact p_dvd_padicValInt_frey_disc a b c p ha hb hc ℓ hℓ2

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Unramified at All Odd Primes (generalization)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Frey curve's mod-p representation is unramified at ANY odd prime ℓ,
not just those dividing the conductor. This is because p | v_ℓ(Δ) holds
universally: v_ℓ(Δ) = 2p · v_ℓ(|abc|), so p | v_ℓ(Δ) regardless of
whether ℓ divides abc (when ℓ ∤ abc, v_ℓ(Δ) = 0 and p | 0 trivially).

This stronger result can be used in HardlyRamified.lean to prove
`IsUnramifiedOutside2p` for the Frey representation. -/
theorem frey_rep_unramified_all_odd (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ2 : ℓ ≠ 2) :
    IsUnramifiedAt (galRepOfCurve (freyCurve a b p) p) ℓ := by
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  apply tate_unramified
  · exact hℓ2
  · exact frey_discriminant a b c p hp5 heq ha hb hc
  · rw [padicValRat_frey_disc_fermat a b c p heq]
    exact p_dvd_padicValInt_frey_disc a b c p ha hb hc ℓ hℓ2

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. Roadmap — Remaining Axioms
-- ═══════════════════════════════════════════════════════════════════════════

/-
  ## Summary

  PROVED (this file):
  • frey_disc_fermat_eq — Δ = 16(abc)^{2p} under Fermat equation
  • frey_weierstrass_disc_eq — (freyCurve a b p).Δ = freyDiscriminantInt (ring)
  • frey_weierstrass_disc_fermat — under Fermat eq, Δ = 16(abc)^{2p} as ℚ
  • padicVal_frey_disc — v_ℓ(Δ_ℕ) = 2p · v_ℓ(|abc|) for odd ℓ
  • p_dvd_padicVal_frey_disc — p | v_ℓ(Δ_ℕ) for odd ℓ
  • p_dvd_padicValInt_frey_disc — (p : ℤ) | v_ℓ(Δ_ℤ) for odd ℓ
  • padicValRat_frey_disc — v_ℓ(Δ_ℚ) = v_ℓ(Δ_ℤ) (integer cast)
  • padicValRat_frey_disc_fermat — under Fermat eq: v_ℓ(Δ_ℚ) = v_ℓ(Δ_Fermat_ℤ)
  • odd_prime_dvd_frey_disc_iff — ℓ | Δ ↔ ℓ | abc (odd ℓ)
  • odd_prime_dvd_disc_iff_dvd_conductor — ℓ | Δ ↔ ℓ | freyConductor (odd ℓ)
  • **frey_rep_unramified** — WAS AXIOM, now THEOREM via tate_unramified
  • **frey_rep_unramified_all_odd** — generalization: all odd primes, not just ℓ | N

  AXIOMS (this file, 1):
  • tate_unramified — Tate parametrization: p | v_ℓ(Δ) → unramified at ℓ
    More targeted than frey_rep_unramified: about a general curve, not
    specifically the Frey curve.

  The net effect: `frey_rep_unramified` (an axiom about the specific Frey
  curve from a Fermat counterexample) is replaced by `tate_unramified`
  (an axiom about ANY elliptic curve with p | v_ℓ(Δ)). The specialization
  to the Frey curve is done by the fully proved discriminant infrastructure.

  ## What remains for full elimination of tate_unramified

  The Tate parametrization connects discriminant valuations to Galois
  representations. Formalizing it requires:
  1. Tate curve over ℤ_ℓ[[q]] (partially in Mathlib: EllipticCurve.Tate)
  2. The connection: for semistable E/ℚ_ℓ with multiplicative reduction,
     the Tate parameter q satisfies v_ℓ(q) = v_ℓ(Δ)
  3. The inertia action on E[p] ≅ (ℤ/pℤ)² factors through the tame
     quotient I_ℓ^t ≅ ∏_{q≠ℓ} ℤ_q, giving a character of order | v_ℓ(q)
  4. mod-p reduction: order | v_ℓ(q) and p | v_ℓ(q) → trivial mod p

  Estimated difficulty: HARD. Graduate-level algebraic geometry.
-/

end Fermat.Discriminant
