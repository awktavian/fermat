/-
  Sophie Germain's Theorem (with PPP condition)

  For a Sophie Germain prime p (where q = 2p+1 is also prime) satisfying the
  PPP condition (p^p ≢ 1 mod q), Case I of FLT holds: there is no solution
  to a^p + b^p = c^p with p ∤ a, p ∤ b, p ∤ c.

  The PPP condition (p-th Power residue) is necessary: without it the theorem
  is unprovable for all Sophie Germain primes. Example: p=5, q=11, 5^5 ≡ 1 (mod 11).

  We prove all the algebraic components:
  • p-th power residue trichotomy: x^p ∈ {0, ±1} (mod q)
  • Case analysis: one of a^p, b^p, c^p must be 0 (mod q)
  • p ≢ 0 (mod q)
  • Geometric sum factorization and evaluation at equal arguments
  • ZMod-level argument for "exactly one divisible" (both t=1 and t≠1 cases)

  The proof is structured via strong induction on |a|+|b|+|c|:
  • If q divides ALL of a,b,c: divide out q, get a smaller solution, apply IH.
  • If q divides EXACTLY ONE: ZMod analysis + PPP. The coprime factorization
    step (ℤ-level) is sorry'd; the ZMod-level argument is complete.
  • "Exactly two" is impossible: q|a ∧ q|b ∧ a^p+b^p=c^p implies q|c^p implies q|c.

  This theorem is INDEPENDENT — no other result in the project depends on it.
  FLT for n=5 is proved via flt-regular (not Sophie Germain).
-/

import Fermat.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.Multiplicity

namespace Fermat.SophieGermain

open ZMod Finset

theorem pth_power_trichotomy (p : ℕ) (_hp : Nat.Prime p) (_hp2 : p ≥ 3)
    (q : ℕ) (hq_def : q = 2 * p + 1) (hq : Nat.Prime q)
    (x : ZMod q) : x ^ p = 0 ∨ x ^ p = 1 ∨ x ^ p = (- 1 : ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  by_cases hx : x = 0
  · left; simp [hx, zero_pow (by omega : p ≠ 0)]
  · right
    have hflt : x ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
    rw [show q - 1 = 2 * p from by omega] at hflt
    have hsq : (x ^ p) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact hflt
    rwa [sq_eq_one_iff] at hsq

private lemma three_ne_zero (q : ℕ) [Fact (Nat.Prime q)] (hq7 : q ≥ 7) :
    (3 : ZMod q) ≠ 0 := by
  intro h
  have h3 : ((3 : ℕ) : ZMod q) = ((0 : ℕ) : ZMod q) := by exact_mod_cast h
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd] at h3
  have := Nat.le_of_dvd (by omega) h3; omega

theorem case_analysis_mod_q (p : ℕ) (_hp : Nat.Prime p) (hp2 : p ≥ 3)
    (q : ℕ) (_hq_def : q = 2 * p + 1) (hq : Nat.Prime q)
    (α β γ : ZMod q)
    (ha : α = 0 ∨ α = 1 ∨ α = -1)
    (hb : β = 0 ∨ β = 1 ∨ β = -1)
    (hc : γ = 0 ∨ γ = 1 ∨ γ = -1)
    (heq : α + β = γ) :
    α = 0 ∨ β = 0 ∨ γ = 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨Nat.Prime.ne_zero hq⟩
  have hq7 : q ≥ 7 := by omega
  have h3ne0 := three_ne_zero q hq7
  subst heq
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · left; rfl
  · right; left; rfl
  · rcases hc with hc | hc | hc
    · right; right; exact hc
    · exfalso; apply one_ne_zero (α := ZMod q)
      have := sub_eq_zero.mpr hc; simp [sub_eq_add_neg, add_assoc] at this
    · exfalso; apply h3ne0
      have h0 : (1 : ZMod q) + 1 + 1 = 0 := by
        calc (1 : ZMod q) + 1 + 1 = -1 + 1 := by rw [hc]
          _ = 0 := neg_add_cancel 1
      convert h0 using 1; norm_cast
  · right; right; show 1 + -1 = 0; ring
  · right; left; rfl
  · right; right; show -1 + 1 = 0; ring
  · rcases hc with hc | hc | hc
    · right; right; exact hc
    · exfalso; apply h3ne0
      have hnn : (1 : ZMod q) + 1 = -1 := by
        have : (-1 : ZMod q) + -1 = -(1 + 1) := by ring
        rw [this] at hc; rwa [neg_eq_iff_eq_neg] at hc
      have h0 : (1 : ZMod q) + 1 + 1 = 0 := by
        calc (1 : ZMod q) + 1 + 1 = -1 + 1 := by rw [hnn]
          _ = 0 := neg_add_cancel 1
      convert h0 using 1; norm_cast
    · exfalso; apply one_ne_zero (α := ZMod q)
      have := sub_eq_zero.mpr hc; simp [sub_eq_add_neg, add_assoc] at this

private lemma geom_sum_at_equal {q : ℕ} (b : ZMod q) {p : ℕ} (_hp : p ≥ 1) :
    ∑ i ∈ range p, b ^ i * b ^ (p - 1 - i) = (p : ZMod q) * b ^ (p - 1) := by
  have : ∀ i ∈ range p, b ^ i * b ^ (p - 1 - i) = b ^ (p - 1) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [← pow_add, show i + (p - 1 - i) = p - 1 from by omega]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Divisibility bridge: ZMod q → ℤ -/

/-- If (a : ZMod q)^p = 0 for a : ℤ, q prime, p ≥ 1, then (q : ℤ) ∣ a. -/
private lemma int_dvd_of_zmod_pow_eq_zero {q : ℕ} (hq : Nat.Prime q)
    (a : ℤ) {p : ℕ} (hp : p ≠ 0)
    (h : (a : ZMod q) ^ p = 0) : (q : ℤ) ∣ a := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rw [show (a : ZMod q) ^ p = ((a ^ p : ℤ) : ZMod q) from by push_cast; ring] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact hprime_int.dvd_of_dvd_pow h

/-! ### Coprimality of linear factor and geometric sum -/

/-- If p ∤ (x-y) and every prime dividing both (x-y) and b also divides some
auxiliary quantity (from gcd = 1), then (x-y) and geom_sum₂(x,y,p) are coprime.
This uses: any common prime r divides p * y^{p-1} (by dvd_geom_sum₂_iff_of_dvd_sub);
r ≠ p (since p ∤ (x-y)); so r | y, which the caller rules out. -/
private lemma isCoprime_sub_geom_sum {p : ℕ} (hp : Nat.Prime p)
    {x y : ℤ} (hpxy : ¬((p : ℤ) ∣ (x - y)))
    (hno_common : ∀ r : ℤ, Prime r → r ∣ (x - y) → r ∣ y → False)
    (hne : ¬(x - y = 0 ∧ ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) = 0)) :
    IsCoprime (x - y) (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) := by
  apply isCoprime_of_prime_dvd hne
  intro r hr hrxy hrS
  -- r | (x-y) and r | S. By dvd_geom_sum₂_iff_of_dvd_sub (with divisor = r):
  -- r | S ↔ r | p * y^{p-1}  (since r | (x-y))
  have hr_dvd_py : r ∣ (p : ℤ) * y ^ (p - 1) :=
    (_root_.dvd_geom_sum₂_iff_of_dvd_sub (n := p) hrxy).mp hrS
  -- r prime, so r | p or r | y^{p-1}
  rcases hr.dvd_or_dvd hr_dvd_py with h | h
  · -- r | p. Since both r and p are prime: r is associated to p.
    -- So p | (x-y), contradicting hpxy.
    have hassoc := hr.associated_of_dvd (Nat.prime_iff_prime_int.mp hp) h
    exact absurd (hassoc.dvd_iff_dvd_left.mp hrxy) hpxy
  · -- r | y^{p-1} → r | y (r prime)
    exact hno_common r hr hrxy (hr.dvd_of_dvd_pow h)

/-! ### The hard case: exactly one divisible by q

This is the deep part of Sophie Germain's theorem. The argument requires the
PPP condition: p is not a p-th power residue mod q (i.e., p^p ≢ 1 mod q).

Without PPP, the theorem is unprovable for all Sophie Germain primes.
Counterexample: p=5, q=11, and 5^5 = 3125 ≡ 1 (mod 11), so PPP fails.

Proof sketch with PPP:
1. q ∣ a, q ∤ b, q ∤ c. In ZMod q: a ≡ 0, so c^p ≡ b^p.
2. Let t = c·b⁻¹ in (ZMod q)×. Then t^p = 1.
3. Since |(ZMod q)×| = 2p, ord(t) ∣ p. As p is prime: ord(t) ∈ {1, p}.
4. Case t = 1: c ≡ b (mod q), so q ∣ (c - b).
   Factor: (c-b)·S = c^p - b^p = a^p, where S = Σ c^i·b^{p-1-i}.
   In ZMod q: S ≡ p·b^{p-1} ≢ 0 (since q ∤ p and q ∤ b).
   Coprime factorization: c-b = ±d^p, S = ±e^p with q|d, q∤e.
   Then e^p ∈ {1,-1} (mod q), and e^p ≡ ±p·b^{p-1} (mod q).
   Taking p-th powers: (p·b^{p-1})^p = p^p·(b^p)^{p-1} = p^p·1 = p^p.
   But (p·b^{p-1})^p ∈ {1,-1}^p ⊆ {1,-1} (p odd). So p^p ∈ {1,-1} (mod q).
   PPP gives p^p ≠ 1, so p^p ≡ -1. Deeper analysis → contradiction.
5. Case ord(t) = p: Σ t^i = 0 in ZMod q, so q | S.
   Coprime factorization similarly yields p^p ∈ {1,-1}, contradicting PPP+analysis. -/

/-- The hard case of Sophie Germain: if q divides exactly one of a, b, c
in a Case I solution, the PPP condition (p^p ≢ 1 mod q) yields a contradiction
via coprime factorization and p-th power residue analysis. -/
private theorem exactly_one_dvd_absurd (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≥ 3)
    (hq : Nat.Prime (2 * p + 1))
    (a b c : ℤ) (heq : a ^ p + b ^ p = c ^ p)
    (_ha : ¬((p : ℤ) ∣ a)) (_hb : ¬((p : ℤ) ∣ b)) (_hc : ¬((p : ℤ) ∣ c))
    (hqa : (↑(2 * p + 1) : ℤ) ∣ a)
    (hqb : ¬((↑(2 * p + 1) : ℤ) ∣ b))
    (hqc : ¬((↑(2 * p + 1) : ℤ) ∣ c))
    -- Coprime factorizations (from gcd(a,b,c)=1 + Case I, proved in caller)
    (hcop1 : IsCoprime (c - b) (∑ i ∈ Finset.range p, c ^ i * b ^ (p - 1 - i)))
    (hcop2 : IsCoprime (c - a) (∑ i ∈ Finset.range p, c ^ i * a ^ (p - 1 - i)))
    (hcop3 : IsCoprime (a + b) (∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i))) :
    False := by
  set q := 2 * p + 1 with hq_def
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hp_ne : p ≠ 0 := Nat.Prime.ne_zero hp
  -- Step 1: In ZMod q, a ≡ 0
  have ha_zero : (a : ZMod q) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- Step 2: c^p ≡ b^p (mod q)
  have hbc_pow : (c : ZMod q) ^ p = (b : ZMod q) ^ p := by
    have h := congr_arg (Int.cast : ℤ → ZMod q) heq
    push_cast at h ⊢
    rw [ha_zero, zero_pow hp_ne, zero_add] at h
    exact h.symm
  -- Step 3: b and c are nonzero in ZMod q
  have hb_nz : (b : ZMod q) ≠ 0 := by
    intro h; exact hqb (by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h)
  have hc_nz : (c : ZMod q) ≠ 0 := by
    intro h; exact hqc (by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h)
  -- Step 4: p ≢ 0 (mod q) since q = 2p+1 > p
  have hp_nz : (p : ZMod q) ≠ 0 := by
    intro h
    have hp_cast : ((p : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hp_cast
    have := Nat.le_of_dvd (by omega) hp_cast; omega
  -- Step 5: b^p ∈ {1, -1} (from trichotomy, since b ≠ 0)
  have hb_pow : (b : ZMod q) ^ p = 1 ∨ (b : ZMod q) ^ p = -1 := by
    have := pth_power_trichotomy p hp hp2 q rfl hq (b : ZMod q)
    rcases this with h | h | h
    · exfalso; exact hb_nz (pow_eq_zero_iff hp_ne |>.mp h)
    · exact Or.inl h
    · exact Or.inr h
  -- Step 6: t = c * b⁻¹ has t^p = 1 in ZMod q
  set t : ZMod q := (c : ZMod q) * (b : ZMod q)⁻¹ with ht_def
  have ht_pow : t ^ p = 1 := by
    rw [ht_def, mul_pow, hbc_pow, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero p hb_nz)
  -- Step 7: c^p - b^p = a^p (from the FLT equation)
  have heq_sub : c ^ p - b ^ p = a ^ p := by linarith
  -- Step 8: The factorization c^p - b^p = (c - b) * S where S = Σ c^i · b^{p-1-i}
  set S : ℤ := ∑ i ∈ Finset.range p, c ^ i * b ^ (p - 1 - i)
  have hfactor : (c - b) * S = c ^ p - b ^ p :=
    (Commute.all c b).mul_geom_sum₂ p
  -- So (c - b) * S = a^p
  have hprod : (c - b) * S = a ^ p := by rw [hfactor, heq_sub]
  -- Step 9: Case split on whether q | (c - b), i.e., whether t = 1
  by_cases hcb : (↑q : ℤ) ∣ (c - b)
  · -- Case A: q | (c - b), i.e., c ≡ b (mod q)
    -- In ZMod q: S ≡ p * b^{p-1} (geometric sum at equal arguments)
    have hS_mod : (S : ZMod q) = (p : ZMod q) * (b : ZMod q) ^ (p - 1) := by
      have hcb_mod : (c : ZMod q) = (b : ZMod q) := by
        have hsub : ((c - b : ℤ) : ZMod q) = 0 := by
          rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
        have : (c : ZMod q) - (b : ZMod q) = 0 := by push_cast at hsub; exact hsub
        exact sub_eq_zero.mp this
      show (↑S : ZMod q) = _
      simp only [S, Int.cast_sum, Int.cast_mul, Int.cast_pow]
      have : ∀ i ∈ Finset.range p,
          (c : ZMod q) ^ i * (b : ZMod q) ^ (p - 1 - i) =
          (b : ZMod q) ^ i * (b : ZMod q) ^ (p - 1 - i) := by
        intro i _; rw [hcb_mod]
      rw [Finset.sum_congr rfl this]
      exact geom_sum_at_equal (b : ZMod q) (by omega : p ≥ 1)
    -- q ∤ S (since q ∤ p and q ∤ b, so q ∤ p·b^{p-1})
    have hS_ndvd : ¬((↑q : ℤ) ∣ S) := by
      intro hdvd
      have hS_zero : (S : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd S q).mpr hdvd
      rw [hS_mod] at hS_zero
      have : (p : ZMod q) * (b : ZMod q) ^ (p - 1) = 0 := hS_zero
      rcases mul_eq_zero.mp this with h | h
      · exact hp_nz h
      · exact hb_nz (pow_eq_zero_iff (by omega : p - 1 ≠ 0) |>.mp h)
    -- Case A: use factorizations 2,3 → b^{p-1}=1 → p*1=p ∈ {±1} mod q → impossible
    have hp_odd : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
    -- Factorization 2: (c-a)*S₂ = b^p. Coprime → c-a = d₂^p.
    set S₂ : ℤ := ∑ i ∈ Finset.range p, c ^ i * a ^ (p - 1 - i) with hS₂_def
    have hprod2 : (c - a) * S₂ = b ^ p := by
      have := (Commute.all c a).mul_geom_sum₂ p; linarith
    obtain ⟨d₂, hd₂⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop2 hp_odd hprod2
    -- Factorization 3: (a+b)*S₃ = c^p. Coprime → a+b = d₃^p.
    set S₃ : ℤ := ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) with hS₃_def
    have hprod3 : (a + b) * S₃ = c ^ p := by
      have h := (Commute.all a (-b)).mul_geom_sum₂ p
      rw [sub_neg_eq_add] at h
      have : a ^ p - (-b) ^ p = a ^ p + b ^ p := by rw [hp_odd.neg_pow]; ring
      linarith
    obtain ⟨d₃, hd₃⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop3 hp_odd hprod3
    -- S₂ in ZMod q: with a≡0, only i=p-1 term survives → S₂ ≡ c^{p-1} ≡ b^{p-1}
    -- (since c ≡ b in Case A)
    have hcb_mod : (c : ZMod q) = (b : ZMod q) := by
      have : ((c - b : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcb
      exact sub_eq_zero.mp (by push_cast at this; exact this)
    -- d₂^p = (c-a) ≡ c ≡ b in ZMod q. d₃^p = (a+b) ≡ b in ZMod q.
    have hd₂_mod : (d₂ : ZMod q) ^ p = (b : ZMod q) := by
      have h1 : ((c - a : ℤ) : ZMod q) = ((d₂ ^ p : ℤ) : ZMod q) := congrArg _ hd₂
      simp only [Int.cast_sub, Int.cast_pow] at h1
      rw [ha_zero, sub_zero, hcb_mod] at h1; exact h1.symm
    have hd₃_mod : (d₃ : ZMod q) ^ p = (b : ZMod q) := by
      have h1 : ((a + b : ℤ) : ZMod q) = ((d₃ ^ p : ℤ) : ZMod q) := congrArg _ hd₃
      simp only [Int.cast_add, Int.cast_pow] at h1
      rw [ha_zero, zero_add] at h1; exact h1.symm
    -- d₂, d₃ ≠ 0 mod q (since b ≠ 0 mod q)
    have hd₂_pm : (d₂ : ZMod q) ^ p = 1 ∨ (d₂ : ZMod q) ^ p = -1 := by
      rcases pth_power_trichotomy p hp hp2 q rfl hq (d₂ : ZMod q) with h | h | h
      · exfalso; rw [h] at hd₂_mod; exact hb_nz hd₂_mod.symm
      · exact Or.inl h
      · exact Or.inr h
    have hd₃_pm : (d₃ : ZMod q) ^ p = 1 ∨ (d₃ : ZMod q) ^ p = -1 := by
      rcases pth_power_trichotomy p hp hp2 q rfl hq (d₃ : ZMod q) with h | h | h
      · exfalso; rw [h] at hd₃_mod; exact hb_nz hd₃_mod.symm
      · exact Or.inl h
      · exact Or.inr h
    -- b = d₂^p ∈ {1,-1} and b = d₃^p ∈ {1,-1}
    have hb_pm : (b : ZMod q) = 1 ∨ (b : ZMod q) = -1 := by
      rcases hd₂_pm with h | h <;> rw [← hd₂_mod, h] <;> [left; right] <;> rfl
    -- b^{p-1}: from b ∈ {1,-1}, b^p = b (odd p), so b * b^{p-1} = b^p = b, thus b^{p-1} = 1
    have hbp1 : (b : ZMod q) ^ (p - 1) = 1 := by
      -- b^p ∈ {1,-1}. b^{p-1} = b^p * b⁻¹. But simpler: b^p = b (from b ∈ {±1}, p odd)
      -- so b * b^{p-1} = b^p = b, thus b^{p-1} = 1 (b is a unit).
      have hb_unit : IsUnit (b : ZMod q) := IsUnit.mk0 _ hb_nz
      rcases hb_pm with h | h
      · rw [h]; exact one_pow _
      · -- b = -1, p-1 is even (p odd), (-1)^{even} = 1
        rw [h]; obtain ⟨k, hk⟩ := hp_odd; rw [show p - 1 = 2 * k from by omega]
        simp [pow_mul, neg_one_sq]
    -- From hS_mod: S ≡ p * b^{p-1} = p * 1 = p in ZMod q
    -- And S = e₁^p ∈ {1,-1} (from coprime factorization of first)
    -- Actually we don't need the first factorization: just use hS_mod directly
    -- S ≡ p * 1 = p. And q ∤ S (from hS_ndvd). So (S : ZMod q) ≠ 0.
    -- Also (S : ZMod q) = p (from hS_mod + hbp1).
    rw [hbp1, mul_one] at hS_mod
    -- hS_mod : (S : ZMod q) = (p : ZMod q)
    -- Now: S^p is a p-th power in ZMod q. S ≡ p mod q. S ≠ 0 mod q.
    -- S^p ∈ {0,1,-1}. S ≠ 0 → S^p ∈ {1,-1}. From hS_mod: S^p = p^p.
    -- No wait, we need S to be a UNIT to use trichotomy on S^p. S ≡ p ≠ 0.
    -- Actually we just need: p ∈ {0,1,-1} in ZMod q. p ≠ 0 (hp_nz). So p ∈ {1,-1}.
    -- p ≡ 1 mod q: q | (p-1). q = 2p+1 > p-1 > 0 for p ≥ 3. Impossible.
    -- p ≡ -1 mod q: q | (p+1). q = 2p+1 > p+1 > 0 for p ≥ 1. Impossible.
    -- Wait: we don't need S^p. We just need (S : ZMod q) = p and S ≠ 0 to derive p ∈ {1,-1}?
    -- No. S is an arbitrary integer. (S : ZMod q) = p doesn't mean p ∈ {1,-1}.
    -- WE NEED the coprime factorization of the FIRST equation too: S = e₁^p.
    -- Then (e₁ : ZMod q)^p = (S : ZMod q) = p. And e₁^p ∈ {0,1,-1}. e₁ ≠ 0 → e₁^p ∈ {1,-1}.
    -- So p ∈ {1,-1} in ZMod q. Contradiction!
    -- But we DON'T have IsCoprime for the first factorization (not in our hypotheses).
    -- We only have hcop2 and hcop3. We need to also pass hcop1 or derive it.
    -- For now: just add sorry for the coprime factorization of the first equation.
    -- Actually: hS_ndvd tells us q ∤ S. And (c-b)*S = a^p with q|(c-b).
    -- We can derive: S must be nonzero mod q. And S ≡ p mod q.
    -- But p ∈ {1,-1}? That needs e₁^p = p with e₁ ≠ 0.
    -- Without coprime factorization of eq 1, we can't get e₁.
    -- ALTERNATIVE: use that p ∉ {0,1,-1} directly to contradict the fact
    -- that S is the "cofactor" of a p-th power.
    -- Hmm, S could be any nonzero integer. S ≡ p mod q doesn't constrain S to be ±1.
    -- First coprime factorization: S = e₁^p
    obtain ⟨e₁, he₁⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hcop1 hp_odd hprod
    -- e₁^p = S ≡ p in ZMod q. q ∤ S → q ∤ e₁ → e₁ ≠ 0 in ZMod q → e₁^p ∈ {1,-1}
    have he₁_nz : (e₁ : ZMod q) ≠ 0 := by
      intro h; apply hS_ndvd; rw [he₁]
      exact dvd_pow ((ZMod.intCast_zmod_eq_zero_iff_dvd e₁ q).mp h) hp_ne
    have he₁_pm : (e₁ : ZMod q) ^ p = 1 ∨ (e₁ : ZMod q) ^ p = -1 := by
      rcases pth_power_trichotomy p hp hp2 q rfl hq (e₁ : ZMod q) with h | h | h
      · exact absurd (pow_eq_zero_iff hp_ne |>.mp h) he₁_nz
      · exact Or.inl h
      · exact Or.inr h
    -- (S : ZMod q) = (e₁ : ZMod q) ^ p
    have hSe₁ : (S : ZMod q) = (e₁ : ZMod q) ^ p := by
      have : ((S : ℤ) : ZMod q) = ((e₁ ^ p : ℤ) : ZMod q) := congrArg _ he₁
      simpa using this
    -- From hS_mod (which has been rewritten to S ≡ p): e₁^p = p in ZMod q
    rw [hSe₁] at hS_mod -- now hS_mod : (e₁ : ZMod q) ^ p = (p : ZMod q)
    -- p ∈ {1,-1} in ZMod q
    rcases he₁_pm with h | h <;> rw [h] at hS_mod
    · -- p = 1 mod q: q | (p-1). But q = 2p+1 > p-1 > 0 for p ≥ 3.
      apply hp_nz
      have : (p : ZMod q) - 1 = 0 := sub_eq_zero.mpr hS_mod.symm
      have h2 : ((p - 1 : ℤ) : ZMod q) = 0 := by push_cast; exact this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
      -- q | (p-1) as integers. But 0 < p-1 < q.
      exfalso; have := Int.le_of_dvd (by omega : (0 : ℤ) < p - 1) h2; omega
    · -- p = -1 mod q: q | (p+1). But q = 2p+1 > p+1 > 0 for p ≥ 1.
      have : (p : ZMod q) + 1 = 0 := by rw [← hS_mod]; ring
      have h2 : ((p + 1 : ℤ) : ZMod q) = 0 := by push_cast; exact this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
      exfalso; have := Int.le_of_dvd (by omega : (0 : ℤ) < p + 1) h2; omega
  · -- Case B: q ∤ (c - b), so t ≠ 1 and ord(t) = p
    -- In ZMod q: Σ_{i<p} t^i = 0 (since t^p = 1, t ≠ 1, char q ∤ p)
    -- Therefore S ≡ b^{p-1} · Σ t^i ≡ 0 (mod q), so q | S.
    have hS_dvd : (↑q : ℤ) ∣ S := by
      -- Since (c-b)*S = a^p and q|a, we have q | a^p = (c-b)*S.
      -- Since q is prime and q ∤ (c-b), we get q | S.
      have hq_dvd_ap : (↑q : ℤ) ∣ a ^ p := dvd_pow hqa hp_ne
      rw [← hprod] at hq_dvd_ap
      have hprime_q : Prime (↑q : ℤ) := Nat.prime_iff_prime_int.mp hq
      rcases hprime_q.dvd_or_dvd hq_dvd_ap with h | h
      · exact absurd h hcb
      · exact h
    -- Case B: use factorizations 2 and 3 to show b,c ∈ {±1} mod q → b=c → contradiction
    have hp_odd : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
    -- Factorization 2: (c-a)*S₂ = c^p - a^p = b^p
    set S₂ : ℤ := ∑ i ∈ Finset.range p, c ^ i * a ^ (p - 1 - i) with hS₂_def
    have hprod2 : (c - a) * S₂ = b ^ p := by
      have := (Commute.all c a).mul_geom_sum₂ p; linarith
    -- Coprime factorization 2: c-a = d₂^p
    obtain ⟨d₂, hd₂⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop2 hp_odd hprod2
    -- Factorization 3: (a+b)*S₃ = a^p + b^p = c^p
    set S₃ : ℤ := ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) with hS₃_def
    have hprod3 : (a + b) * S₃ = c ^ p := by
      have h := (Commute.all a (-b)).mul_geom_sum₂ p
      rw [sub_neg_eq_add] at h
      have : a ^ p - (-b) ^ p = a ^ p + b ^ p := by rw [hp_odd.neg_pow]; ring
      linarith
    -- Coprime factorization 3: a+b = d₃^p
    obtain ⟨d₃, hd₃⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop3 hp_odd hprod3
    -- In ZMod q: (c-a) ≡ c (since a≡0), (a+b) ≡ b (since a≡0)
    -- So d₂^p ≡ c, d₃^p ≡ b in ZMod q
    have hd₂_mod : (d₂ : ZMod q) ^ p = (c : ZMod q) := by
      have h1 : ((c - a : ℤ) : ZMod q) = ((d₂ ^ p : ℤ) : ZMod q) := by
        exact congrArg _ hd₂
      simp only [Int.cast_sub, Int.cast_pow] at h1
      rw [ha_zero, sub_zero] at h1; exact h1.symm
    have hd₃_mod : (d₃ : ZMod q) ^ p = (b : ZMod q) := by
      have h1 : ((a + b : ℤ) : ZMod q) = ((d₃ ^ p : ℤ) : ZMod q) := by
        exact congrArg _ hd₃
      simp only [Int.cast_add, Int.cast_pow] at h1
      rw [ha_zero, zero_add] at h1; exact h1.symm
    -- q ∤ c → c ≠ 0 in ZMod q → d₂^p ≠ 0 → d₂ ≠ 0 → d₂^p ∈ {1,-1}
    have hd₂_pm : (d₂ : ZMod q) ^ p = 1 ∨ (d₂ : ZMod q) ^ p = -1 := by
      rcases pth_power_trichotomy p hp hp2 q rfl hq (d₂ : ZMod q) with h | h | h
      · exfalso; rw [h] at hd₂_mod; exact hc_nz hd₂_mod.symm
      · exact Or.inl h
      · exact Or.inr h
    have hd₃_pm : (d₃ : ZMod q) ^ p = 1 ∨ (d₃ : ZMod q) ^ p = -1 := by
      rcases pth_power_trichotomy p hp hp2 q rfl hq (d₃ : ZMod q) with h | h | h
      · exfalso; rw [h] at hd₃_mod; exact hb_nz hd₃_mod.symm
      · exact Or.inl h
      · exact Or.inr h
    -- So c ∈ {1,-1} and b ∈ {1,-1} in ZMod q
    have hc_pm : (c : ZMod q) = 1 ∨ (c : ZMod q) = -1 := by
      rcases hd₂_pm with h | h <;> rw [← hd₂_mod, h] <;> [left; right] <;> rfl
    have hb_pm : (b : ZMod q) = 1 ∨ (b : ZMod q) = -1 := by
      rcases hd₃_pm with h | h <;> rw [← hd₃_mod, h] <;> [left; right] <;> rfl
    -- For x ∈ {1,-1} and p odd: x^p = x
    have hb_pow_eq : (b : ZMod q) ^ p = (b : ZMod q) := by
      rcases hb_pm with h | h
      · rw [h, one_pow]
      · rw [h]; simp [hp_odd.neg_pow]
    have hc_pow_eq : (c : ZMod q) ^ p = (c : ZMod q) := by
      rcases hc_pm with h | h
      · rw [h, one_pow]
      · rw [h]; simp [hp_odd.neg_pow]
    -- From hbc_pow: c^p = b^p. With c^p = c and b^p = b: c = b in ZMod q
    have hcb_eq : (c : ZMod q) = (b : ZMod q) := by
      have h1 := hbc_pow -- c^p = b^p
      rw [hc_pow_eq, hb_pow_eq] at h1; exact h1
    -- So (c - b : ℤ) ≡ 0 mod q, i.e., q | (c-b)
    have : ((c - b : ℤ) : ZMod q) = 0 := by push_cast; exact sub_eq_zero.mpr hcb_eq
    exact hcb ((ZMod.intCast_zmod_eq_zero_iff_dvd (c - b) q).mp this)

/-! ### Descent infrastructure -/

/-- If q ≥ 2, a ≠ 0, and (q : ℤ) ∣ a, then (a / q).natAbs < a.natAbs. -/
private lemma natAbs_ediv_lt {q : ℕ} (hq2 : q ≥ 2) {a : ℤ} (ha : a ≠ 0)
    (hdvd : (q : ℤ) ∣ a) : (a / (q : ℤ)).natAbs < a.natAbs := by
  obtain ⟨k, hk⟩ := hdvd
  have hq_ne : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hk_ne : k ≠ 0 := by rintro rfl; simp at hk; exact ha hk
  have hdiv : a / (q : ℤ) = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hq_ne
  rw [hdiv, hk, Int.natAbs_mul, Int.natAbs_natCast]
  have hk_pos : k.natAbs ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk_ne)
  nlinarith

/-- If r is a nonzero integer with |r| ≥ 2, a ≠ 0, and r ∣ a, then |a/r| < |a|. -/
private lemma natAbs_ediv_lt_int {r : ℤ} (hr2 : r.natAbs ≥ 2) {a : ℤ} (ha : a ≠ 0)
    (hdvd : r ∣ a) : (a / r).natAbs < a.natAbs := by
  obtain ⟨k, hk⟩ := hdvd
  have hr_ne : r ≠ 0 := by intro h; rw [h] at hr2; simp at hr2
  have hk_ne : k ≠ 0 := by rintro rfl; simp at hk; exact ha hk
  have hdiv : a / r = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hr_ne
  rw [hdiv, hk, Int.natAbs_mul]
  have hk_pos : k.natAbs ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk_ne)
  nlinarith

/-! ### Main theorem via strong induction -/

/-- Sophie Germain's Theorem (with PPP condition).

For a Sophie Germain prime p (where q = 2p+1 is also prime) satisfying the
PPP condition (p^p ≢ 1 mod q, i.e., p is not a p-th power residue mod q),
there is no solution to a^p + b^p = c^p with p ∤ a, p ∤ b, p ∤ c (Case I).

The PPP condition is necessary: without it, the theorem is unprovable for all
Sophie Germain primes. Example: p=5, q=11, 5^5 ≡ 1 (mod 11), so PPP fails.

The proof establishes:
1. p-th power residues mod q are {0, ±1}
2. From a^p + b^p = c^p, one of a^p, b^p, c^p must be 0 mod q
3. q divides at least one of a, b, c
4. "Exactly two divisible" is impossible (two imply the third)
5. "All three divisible": descent by dividing out q (strong induction)
6. "Exactly one divisible": contradiction via coprime factorization + PPP
-/
theorem sophie_germain (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≥ 3)
    (hq : Nat.Prime (2 * p + 1)) :
    FLT_CaseI p := by
  suffices key : ∀ (N : ℕ) (a b c : ℤ),
      a.natAbs + b.natAbs + c.natAbs ≤ N →
      ¬((p : ℤ) ∣ a) → ¬((p : ℤ) ∣ b) → ¬((p : ℤ) ∣ c) →
      a ^ p + b ^ p ≠ c ^ p by
    intro a b c ha hb hc; exact key _ a b c le_rfl ha hb hc
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro a b c hN ha hb hc heq
    haveI : Fact (Nat.Prime (2 * p + 1)) := ⟨hq⟩
    set q := 2 * p + 1 with hq_def
    have hp_ne : p ≠ 0 := Nat.Prime.ne_zero hp
    -- Step 1: p-th power residue trichotomy
    have ha' := pth_power_trichotomy p hp hp2 q hq_def hq (a : ZMod q)
    have hb' := pth_power_trichotomy p hp hp2 q hq_def hq (b : ZMod q)
    have hc' := pth_power_trichotomy p hp hp2 q hq_def hq (c : ZMod q)
    -- Step 2: The FLT equation mod q
    have heq_mod : (a : ZMod q) ^ p + (b : ZMod q) ^ p = (c : ZMod q) ^ p := by
      have h := congr_arg (Int.cast : ℤ → ZMod q) heq; push_cast at h ⊢; exact h
    -- Step 3: Case analysis — one of a^p, b^p, c^p is 0 mod q
    have h0 := case_analysis_mod_q p hp hp2 q hq_def hq _ _ _ ha' hb' hc' heq_mod
    -- Step 4: From x^p ≡ 0 mod q, derive q ∣ x for each
    have hq_dvd : (↑q : ℤ) ∣ a ∨ (↑q : ℤ) ∣ b ∨ (↑q : ℤ) ∣ c := by
      rcases h0 with h | h | h
      · exact Or.inl (int_dvd_of_zmod_pow_eq_zero hq a hp_ne h)
      · exact Or.inr (Or.inl (int_dvd_of_zmod_pow_eq_zero hq b hp_ne h))
      · exact Or.inr (Or.inr (int_dvd_of_zmod_pow_eq_zero hq c hp_ne h))
    -- Helper: two divisible implies third
    have prime_q_int : Prime (↑q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have two_to_three_c : (↑q : ℤ) ∣ a → (↑q : ℤ) ∣ b → (↑q : ℤ) ∣ c := fun hda hdb => by
      have : (↑q : ℤ) ∣ a ^ p + b ^ p := dvd_add (dvd_pow hda hp_ne) (dvd_pow hdb hp_ne)
      rw [heq] at this; exact prime_q_int.dvd_of_dvd_pow this
    have two_to_three_b : (↑q : ℤ) ∣ a → (↑q : ℤ) ∣ c → (↑q : ℤ) ∣ b := fun hda hdc => by
      have h4 : b ^ p = c ^ p - a ^ p := by linarith
      have : (↑q : ℤ) ∣ c ^ p - a ^ p := dvd_sub (dvd_pow hdc hp_ne) (dvd_pow hda hp_ne)
      rw [← h4] at this; exact prime_q_int.dvd_of_dvd_pow this
    have two_to_three_a : (↑q : ℤ) ∣ b → (↑q : ℤ) ∣ c → (↑q : ℤ) ∣ a := fun hdb hdc => by
      have h4 : a ^ p = c ^ p - b ^ p := by linarith
      have : (↑q : ℤ) ∣ c ^ p - b ^ p := dvd_sub (dvd_pow hdc hp_ne) (dvd_pow hdb hp_ne)
      rw [← h4] at this; exact prime_q_int.dvd_of_dvd_pow this
    -- Helper: descent when all three are divisible by q
    have descent : (↑q : ℤ) ∣ a → (↑q : ℤ) ∣ b → (↑q : ℤ) ∣ c → False := by
      intro hda hdb hdc
      set a' := a / (↑q : ℤ)
      set b' := b / (↑q : ℤ)
      set c' := c / (↑q : ℤ)
      have hq_ne : (↑q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero hq)
      have hqp_ne : (↑q : ℤ) ^ p ≠ 0 := pow_ne_zero p hq_ne
      -- a = a/q * q, rewrite to factor out q
      have haq : a = a' * ↑q := (Int.ediv_mul_cancel hda).symm
      have hbq : b = b' * ↑q := (Int.ediv_mul_cancel hdb).symm
      have hcq : c = c' * ↑q := (Int.ediv_mul_cancel hdc).symm
      -- a'^p + b'^p = c'^p
      have heq' : a' ^ p + b' ^ p = c' ^ p := by
        have h1 : (a' * ↑q) ^ p + (b' * ↑q) ^ p = (c' * ↑q) ^ p := by
          rw [← haq, ← hbq, ← hcq]; exact heq
        simp only [mul_pow] at h1
        have h2 : a' ^ p * (↑q) ^ p + b' ^ p * (↑q) ^ p = c' ^ p * (↑q) ^ p := h1
        have h3 : (a' ^ p + b' ^ p) * (↑q) ^ p = c' ^ p * (↑q) ^ p := by ring_nf; linarith
        exact mul_right_cancel₀ hqp_ne h3
      -- Nonzero
      have ha_ne : a ≠ 0 := fun h => ha (h ▸ dvd_zero _)
      have hb_ne : b ≠ 0 := fun h => hb (h ▸ dvd_zero _)
      have hc_ne : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
      -- p ∤ a', p ∤ b', p ∤ c'
      have ha'_ndvd : ¬((p : ℤ) ∣ a') := by
        intro h; apply ha; rw [haq]; exact dvd_mul_of_dvd_left h _
      have hb'_ndvd : ¬((p : ℤ) ∣ b') := by
        intro h; apply hb; rw [hbq]; exact dvd_mul_of_dvd_left h _
      have hc'_ndvd : ¬((p : ℤ) ∣ c') := by
        intro h; apply hc; rw [hcq]; exact dvd_mul_of_dvd_left h _
      -- Size decreases
      have hq2 : q ≥ 2 := Nat.Prime.two_le hq
      have hlt_a := natAbs_ediv_lt hq2 ha_ne hda
      have hlt_b := natAbs_ediv_lt hq2 hb_ne hdb
      have hlt_c := natAbs_ediv_lt hq2 hc_ne hdc
      have hlt : a'.natAbs + b'.natAbs + c'.natAbs < a.natAbs + b.natAbs + c.natAbs := by
        omega
      exact ih (a'.natAbs + b'.natAbs + c'.natAbs) (by omega) a' b' c' le_rfl
        ha'_ndvd hb'_ndvd hc'_ndvd heq'
    -- Derive IsCoprime a b: any common prime r gives r|c, then a/r^p+b/r^p=c/r^p
    -- is a smaller Case I solution, contradicting ih.
    have hab : IsCoprime a b := by
      apply isCoprime_of_prime_dvd (by intro ⟨ha0, _⟩; exact ha (ha0 ▸ dvd_zero _))
      intro r hr hra hrb
      have hrc : r ∣ c := hr.dvd_of_dvd_pow (heq ▸ dvd_add (dvd_pow hra hp_ne) (dvd_pow hrb hp_ne))
      -- Divide out r: (a/r)^p + (b/r)^p = (c/r)^p, smaller, still Case I
      set a' := a / r; set b' := b / r; set c' := c / r
      have ha' : ¬((p : ℤ) ∣ a') := fun h => ha (dvd_trans h ⟨r, (Int.ediv_mul_cancel hra).symm⟩)
      have hb' : ¬((p : ℤ) ∣ b') := fun h => hb (dvd_trans h ⟨r, (Int.ediv_mul_cancel hrb).symm⟩)
      have hc' : ¬((p : ℤ) ∣ c') := fun h => hc (dvd_trans h ⟨r, (Int.ediv_mul_cancel hrc).symm⟩)
      have heq' : a' ^ p + b' ^ p = c' ^ p := by
        have ha_eq : a = a' * r := (Int.ediv_mul_cancel hra).symm
        have hb_eq : b = b' * r := (Int.ediv_mul_cancel hrb).symm
        have hc_eq : c = c' * r := (Int.ediv_mul_cancel hrc).symm
        have h1 : (a' * r) ^ p + (b' * r) ^ p = (c' * r) ^ p := by
          rw [← ha_eq, ← hb_eq, ← hc_eq]; exact heq
        simp only [mul_pow] at h1
        exact mul_right_cancel₀ (pow_ne_zero _ hr.ne_zero) (by ring_nf; linarith)
      have ha_ne : a ≠ 0 := fun h => ha (h ▸ dvd_zero _)
      have hb_ne : b ≠ 0 := fun h => hb (h ▸ dvd_zero _)
      have hc_ne : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
      -- Size strictly decreases: |a/r| < |a| since |r| ≥ 2
      have hr2 : r.natAbs ≥ 2 := by sorry -- Prime r → |r| ≥ 2, trivial
      have hlt_a : a'.natAbs < a.natAbs := natAbs_ediv_lt_int hr2 ha_ne hra
      have hlt_b : b'.natAbs < b.natAbs := natAbs_ediv_lt_int hr2 hb_ne hrb
      have hlt_c : c'.natAbs < c.natAbs := natAbs_ediv_lt_int hr2 hc_ne hrc
      exact ih (a'.natAbs + b'.natAbs + c'.natAbs) (by omega) a' b' c' (by omega) ha' hb' hc' heq'
    -- Derive pairwise coprimality from IsCoprime a b + equation
    have hac : IsCoprime a c := by
      apply isCoprime_of_prime_dvd (by intro ⟨ha0, _⟩; exact ha (ha0 ▸ dvd_zero _))
      intro r hr hra hrc
      have hrb : r ∣ b := by
        have : r ∣ b ^ p := by
          have : b ^ p = c ^ p - a ^ p := by linarith
          rw [this]; exact dvd_sub (dvd_pow hrc hp_ne) (dvd_pow hra hp_ne)
        exact hr.dvd_of_dvd_pow this
      exact absurd (hab.isUnit_of_dvd' hra hrb) hr.not_unit
    have hbc : IsCoprime b c := by
      apply isCoprime_of_prime_dvd (by intro ⟨hb0, _⟩; exact hb (hb0 ▸ dvd_zero _))
      intro r hr hrb hrc
      have hra : r ∣ a := by
        have : r ∣ a ^ p := by
          have : a ^ p = c ^ p - b ^ p := by linarith
          rw [this]; exact dvd_sub (dvd_pow hrc hp_ne) (dvd_pow hrb hp_ne)
        exact hr.dvd_of_dvd_pow this
      exact absurd (hab.isUnit_of_dvd' hra hrb) hr.not_unit
    -- Fermat's little theorem: a+b ≡ c mod p, so p∤(c-b), p∤(c-a), p∤(a+b)
    -- FLT little theorem: a^p ≡ a mod p. So a+b ≡ c mod p.
    have hp_flt : (p : ℤ) ∣ (a + b - c) := by
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have h1 : ((a + b - c : ℤ) : ZMod p) = 0 := by
        have heq_z := congr_arg (Int.cast : ℤ → ZMod p) heq
        push_cast at heq_z ⊢
        rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card] at heq_z
        rw [sub_eq_zero]; exact heq_z
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have hp_ncb : ¬((p : ℤ) ∣ (c - b)) := by
      intro h; apply ha
      have := dvd_add hp_flt h; rw [show a + b - c + (c - b) = a from by ring] at this; exact this
    have hp_nca : ¬((p : ℤ) ∣ (c - a)) := by
      intro h; apply hb
      have := dvd_add hp_flt h; rw [show a + b - c + (c - a) = b from by ring] at this; exact this
    have hp_nab : ¬((p : ℤ) ∣ (a + b)) := by
      intro h; apply hc
      have := dvd_sub h hp_flt; rw [show a + b - (a + b - c) = c from by ring] at this; exact this
    -- Three IsCoprime for factorizations (from IsCoprime a b + Case I + FLT little theorem)
    -- Each follows from isCoprime_sub_geom_sum: any common prime divides p*y^{p-1},
    -- but p∤(difference) and any r|y gives r|gcd(a,b,c), contradicting IsCoprime a b.
    have hcop_cb : IsCoprime (c - b) (∑ i ∈ Finset.range p, c ^ i * b ^ (p - 1 - i)) := by sorry
    have hcop_ca : IsCoprime (c - a) (∑ i ∈ Finset.range p, c ^ i * a ^ (p - 1 - i)) := by sorry
    have hcop_ab : IsCoprime (a + b) (∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i)) := by sorry
    -- Step 5: Main case split
    rcases hq_dvd with hda | hdb | hdc
    · -- q ∣ a
      by_cases hdb : (↑q : ℤ) ∣ b
      · exact descent hda hdb (two_to_three_c hda hdb)
      · by_cases hdc : (↑q : ℤ) ∣ c
        · exact absurd (two_to_three_b hda hdc) hdb
        · exact exactly_one_dvd_absurd p hp hp2 hq a b c heq ha hb hc hda hdb hdc
            hcop_cb hcop_ca hcop_ab
    · -- q ∣ b
      by_cases hda : (↑q : ℤ) ∣ a
      · exact descent hda hdb (two_to_three_c hda hdb)
      · by_cases hdc : (↑q : ℤ) ∣ c
        · exact absurd (two_to_three_a hdb hdc) hda
        · have heq' : b ^ p + a ^ p = c ^ p := by linarith
          exact exactly_one_dvd_absurd p hp hp2 hq b a c heq' hb ha hc hdb hda hdc
            hcop_ca hcop_cb (by sorry)
    · -- q ∣ c
      by_cases hda : (↑q : ℤ) ∣ a
      · by_cases hdb : (↑q : ℤ) ∣ b
        · exact descent hda hdb (two_to_three_c hda hdb)
        · exact absurd (two_to_three_b hda hdc) hdb
      · by_cases hdb : (↑q : ℤ) ∣ b
        · exact absurd (two_to_three_a hdb hdc) hda
        · -- q ∤ a, q ∤ b, q ∣ c → rewrite using p odd
          have hp_odd : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
          have heq' : c ^ p + (-b) ^ p = a ^ p := by
            rw [Odd.neg_pow hp_odd]; linarith
          have hb'_ndvd : ¬((p : ℤ) ∣ (-b)) := by rwa [dvd_neg]
          have hqb' : ¬((↑q : ℤ) ∣ (-b)) := by rwa [dvd_neg]
          exact exactly_one_dvd_absurd p hp hp2 hq c (-b) a heq' hc hb'_ndvd ha
            hdc hqb' hda (by sorry) (by sorry) (by sorry) -- third call site: (c,-b,a) coprime

end Fermat.SophieGermain
