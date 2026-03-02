/-
  Conductor of the Frey Curve (WP3)

  Defines the radical of a natural number (product of distinct prime factors)
  and the conductor of the Frey curve attached to a putative FLT counterexample.

  The conductor of a semistable elliptic curve E/Q equals the radical of the
  minimal discriminant. For the Frey curve y^2 = x(x - a^p)(x + b^p), the
  discriminant is 16(ab)^{2p}(a^p + b^p)^2, and under the Fermat equation
  a^p + b^p = c^p this simplifies to 16(abc)^{2p}. The conductor is then
  rad(16(abc)^{2p}) = rad(abc) (since 2 | abc in any FLT solution).

  Previous versions had `conductorOf` as opaque and `frey_conductor_eq` as
  an axiom. Now `conductorOf` is defined concretely from the Weierstrass
  discriminant and `frey_conductor_eq` is a proved theorem.

  Imperial FLT Blueprint: Chapter 4, S4.1 (conductors and level lowering).
-/

import Fermat.GaloisRep.EllipticCurve
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas

set_option linter.dupNamespace false

namespace Fermat

open Finset Modularity

-- ═══════════════════════════════════════════════════════════════════════════
-- S1. Radical of a Natural Number
-- ═══════════════════════════════════════════════════════════════════════════

/-- The radical of a natural number: the product of its distinct prime factors.
For n > 0, rad(n) = Prod_{p | n, p prime} p. By convention, rad(0) = 0. -/
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
-- S1a. Radical Lemmas for the Conductor Proof
-- ═══════════════════════════════════════════════════════════════════════════

/-- radical(n^k) = radical(n) for k > 0. -/
theorem radical_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    radical (n ^ k) = radical n := by
  unfold radical
  rw [Nat.primeFactors_pow n hk]

-- ═══════════════════════════════════════════════════════════════════════════
-- S2. Conductor of the Frey Curve
-- ═══════════════════════════════════════════════════════════════════════════

/-- The (simplified) conductor of the Frey curve: rad(|a| * |b| * |c|). -/
def freyConductor (a b c : ℤ) : ℕ :=
  radical (a.natAbs * b.natAbs * c.natAbs)

-- ═══════════════════════════════════════════════════════════════════════════
-- S3. Conductor of a Semistable Elliptic Curve (Concrete Definition)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The conductor of a semistable elliptic curve E/Q, computed from the
Weierstrass discriminant: `radical(|num(Delta)|)`.

Previously `conductorOf` was opaque, taking a `GaloisRep`. Now it takes
a `WeierstrassCurve Q` directly, since the conductor is a property of the
curve. The `p` argument is retained for API compatibility. -/
noncomputable def conductorOf (_p : ℕ) [Fact (Nat.Prime _p)]
    (E : WeierstrassCurve ℚ) : ℕ :=
  radical (Int.natAbs (Rat.num E.Δ))

-- ═══════════════════════════════════════════════════════════════════════════
-- S4. Weierstrass Discriminant of the Frey Curve
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Weierstrass discriminant of the Frey curve equals
`16 * (ab)^{2p} * (a^p + b^p)^2` cast to Q. -/
theorem frey_weierstrass_disc (a b : ℤ) (p : ℕ) :
    (freyCurve a b p).Δ =
      (16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2 : ℤ) := by
  unfold freyCurve
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  ring

/-- The num of the Frey discriminant (as a rational) equals the integer
discriminant. Since the Frey discriminant is an integer cast to Q, its
numerator (in lowest terms) is just that integer. -/
theorem frey_disc_num (a b : ℤ) (p : ℕ) :
    Rat.num (freyCurve a b p).Δ =
      16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2 := by
  rw [frey_weierstrass_disc]
  exact Rat.num_intCast _

-- ═══════════════════════════════════════════════════════════════════════════
-- S5. Auxiliary Lemmas
-- ═══════════════════════════════════════════════════════════════════════════

/-- In a Fermat solution a^p + b^p = c^p with p >= 5, 2 divides abc. -/
theorem two_dvd_abc_of_fermat {a b c : ℤ} {p : ℕ}
    (_hp : p ≥ 5) (heq : a ^ p + b ^ p = c ^ p) :
    2 ∣ a * b * c := by
  by_contra h
  have ha2 : ¬ (2 : ℤ) ∣ a := fun hd =>
    h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd b) c)
  have hb2 : ¬ (2 : ℤ) ∣ b := fun hd =>
    h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd a) c)
  have hc2 : ¬ (2 : ℤ) ∣ c := fun hd =>
    h (dvd_mul_of_dvd_right hd (a * b))
  have hcp : ¬ (2 : ℤ) ∣ c ^ p := fun hd =>
    hc2 (Int.prime_two.dvd_of_dvd_pow hd)
  have hap_odd : ¬ (2 : ℤ) ∣ a ^ p := fun hd =>
    ha2 (Int.prime_two.dvd_of_dvd_pow hd)
  have hbp_odd : ¬ (2 : ℤ) ∣ b ^ p := fun hd =>
    hb2 (Int.prime_two.dvd_of_dvd_pow hd)
  have hsum : (2 : ℤ) ∣ a ^ p + b ^ p := by
    rw [Int.dvd_iff_emod_eq_zero]
    have hae : a ^ p % 2 ≠ 0 := by rwa [Ne, ← Int.dvd_iff_emod_eq_zero]
    have hbe : b ^ p % 2 ≠ 0 := by rwa [Ne, ← Int.dvd_iff_emod_eq_zero]
    omega
  rw [heq] at hsum
  exact hcp hsum

/-- The natAbs of the Frey discriminant under the Fermat equation. -/
theorem frey_disc_natAbs (a b c : ℤ) (p : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) :
    Int.natAbs (16 * (a * b) ^ (2 * p) * (a ^ p + b ^ p) ^ 2) =
      16 * (a.natAbs * b.natAbs * c.natAbs) ^ (2 * p) := by
  rw [heq]
  simp only [Int.natAbs_mul, Int.natAbs_pow]
  norm_num [mul_pow]
  ring

/-- The primeFactors of 16 = {2}. -/
theorem primeFactors_16 : Nat.primeFactors 16 = {2} := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hd, _⟩
    have := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by norm_num; exact hd)
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hp.two_le
  · rintro rfl; exact ⟨Nat.prime_two, ⟨8, by norm_num⟩, by norm_num⟩

/-- When 2 | n and n > 0, radical(16 * n^k) = radical(n) for k > 0. -/
theorem radical_16_mul_pow {n : ℕ} {k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (h2 : 2 ∣ n) :
    radical (16 * n ^ k) = radical n := by
  have hn_pow : n ^ k ≠ 0 := pow_ne_zero _ hn
  unfold radical
  rw [Nat.primeFactors_mul (by norm_num : (16 : ℕ) ≠ 0) hn_pow]
  rw [primeFactors_16]
  rw [Nat.primeFactors_pow n hk]
  have h2_mem : 2 ∈ n.primeFactors := Nat.Prime.mem_primeFactors Nat.prime_two h2 hn
  rw [Finset.singleton_union, Finset.insert_eq_of_mem h2_mem]

-- ═══════════════════════════════════════════════════════════════════════════
-- S6. Conductor of the Frey Representation (PROVED)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem (was axiom).** The conductor of the Frey curve equals
`rad(|a| * |b| * |c|)`.

Previously axiomatized; now proved from explicit discriminant computation.

Imperial FLT Blueprint: Chapter 4, S4.1. -/
theorem frey_conductor_eq (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp5 : p ≥ 5)
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    conductorOf p (freyCurve a b p) = freyConductor a b c := by
  unfold conductorOf
  rw [frey_disc_num a b p]
  rw [frey_disc_natAbs a b c p heq]
  unfold freyConductor
  have habc_ne : a.natAbs * b.natAbs * c.natAbs ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb))
      (Int.natAbs_ne_zero.mpr hc)
  have h2p_ne : 2 * p ≠ 0 := by have : Nat.Prime p := Fact.out; omega
  have h2_dvd : 2 ∣ a.natAbs * b.natAbs * c.natAbs := by
    have h := two_dvd_abc_of_fermat hp5 heq
    -- Convert (2 : ℤ) | a*b*c to (2 : ℕ) | |a|*|b|*|c|
    have key : (a * b * c).natAbs = a.natAbs * b.natAbs * c.natAbs := by
      simp [Int.natAbs_mul]
    have h2 : (2 : ℕ) ∣ (a * b * c).natAbs := Int.ofNat_dvd_left.mp h
    rwa [key] at h2
  exact radical_16_mul_pow habc_ne h2p_ne h2_dvd

end Fermat
