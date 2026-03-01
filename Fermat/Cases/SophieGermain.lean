/-
  Sophie Germain's Theorem

  For a Sophie Germain prime p (where q = 2p+1 is also prime),
  Case I of FLT holds: there is no solution to a^p + b^p = c^p
  with p ∤ a, p ∤ b, p ∤ c.

  We prove all the algebraic components:
  • p-th power residue trichotomy: x^p ∈ {0, ±1} (mod q)
  • Case analysis: one of a^p, b^p, c^p must be 0 (mod q)
  • p ≢ 0 (mod q)
  • Geometric sum identity for equal arguments

  The proof is structured via strong induction on |a|+|b|+|c|:
  • If q divides ALL of a,b,c: divide out q, get a smaller solution, apply IH.
  • If q divides EXACTLY ONE: this requires the Lifting the Exponent Lemma
    and v_q valuation analysis. This case is isolated in a single sorry'd lemma.
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

/-! ### The hard case: exactly one divisible by q

This is the deep part of Sophie Germain's theorem requiring the Lifting the
Exponent Lemma (LTE). The argument proceeds:

1. WLOG q ∣ a, q ∤ b, q ∤ c. Then b^p ≡ c^p (mod q), both nonzero.
2. Let t = c·b⁻¹ in (ℤ/qℤ)×. Then t^p ≡ 1 (mod q).
3. Since |(ℤ/qℤ)×| = 2p, ord(t) ∣ p. As p is prime, ord(t) ∈ {1, p}.
4. If ord(t) = 1, then c ≡ b (mod q), so q ∣ (c - b).
   By LTE: v_q(c^p - b^p) = v_q(c - b) + v_q(p) = v_q(c - b) (since q ∤ p).
   But v_q(a^p) = p · v_q(a) ≥ p. So v_q(c - b) ≥ p.
   The geometric sum Σ c^i · b^(p-1-i) ≡ p · b^(p-1) ≢ 0 (mod q),
   so v_q(geometric sum) = 0. Then v_q(c^p - b^p) = v_q(c - b) + 0 = v_q(c - b).
   This gives v_q(c - b) = p · v_q(a) ≥ p, consistent so far.
   The contradiction comes from examining the equation modulo higher powers of q.
5. If ord(t) = p, then t ≠ ±1 (since p ≥ 3), so c ≢ ±b (mod q).
   Then q ∤ (c - b) and q ∤ (c + b). The factorization
   c^p - b^p = (c - b) · Σ c^i · b^(p-1-i) gives v_q(c^p - b^p) = 0
   (both factors are coprime to q). But v_q(a^p) ≥ p ≥ 3. Contradiction.

The full formalization requires ~200 lines of valuation theory and LTE.
Since this theorem is independent (FLT for n=5 uses flt-regular), we
isolate the sorry here. -/

/-- The hard case of Sophie Germain: if q divides exactly one of a, b, c
in a Case I solution, derive a contradiction via LTE and valuation analysis. -/
private theorem exactly_one_dvd_absurd (p : ℕ) (_hp : Nat.Prime p) (_hp2 : p ≥ 3)
    (_hq : Nat.Prime (2 * p + 1))
    (a b c : ℤ) (_heq : a ^ p + b ^ p = c ^ p)
    (_ha : ¬((p : ℤ) ∣ a)) (_hb : ¬((p : ℤ) ∣ b)) (_hc : ¬((p : ℤ) ∣ c))
    (_hqa : (↑(2 * p + 1) : ℤ) ∣ a)
    (_hqb : ¬((↑(2 * p + 1) : ℤ) ∣ b))
    (_hqc : ¬((↑(2 * p + 1) : ℤ) ∣ c)) :
    False := by
  sorry

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

/-! ### Main theorem via strong induction -/

/-- Sophie Germain's Theorem.

For a Sophie Germain prime p (where q = 2p+1 is also prime),
there is no solution to a^p + b^p = c^p with p ∤ a, p ∤ b, p ∤ c (Case I).

The proof establishes:
1. p-th power residues mod q are {0, ±1}
2. From a^p + b^p = c^p, one of a^p, b^p, c^p must be 0 mod q
3. q divides at least one of a, b, c
4. "Exactly two divisible" is impossible (two imply the third)
5. "All three divisible": descent by dividing out q (strong induction)
6. "Exactly one divisible": contradiction via LTE (sorry'd sub-lemma)
-/
theorem sophie_germain (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≥ 3)
    (hq : Nat.Prime (2 * p + 1)) :
    FLT_CaseI p := by
  -- We prove by strong induction on |a| + |b| + |c| that no Case I solution exists.
  suffices key : ∀ (N : ℕ) (a b c : ℤ),
      a.natAbs + b.natAbs + c.natAbs ≤ N →
      ¬((p : ℤ) ∣ a) → ¬((p : ℤ) ∣ b) → ¬((p : ℤ) ∣ c) →
      a ^ p + b ^ p ≠ c ^ p by
    intro a b c ha hb hc
    exact key _ a b c le_rfl ha hb hc
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
    -- Step 5: Main case split
    rcases hq_dvd with hda | hdb | hdc
    · -- q ∣ a
      by_cases hdb : (↑q : ℤ) ∣ b
      · exact descent hda hdb (two_to_three_c hda hdb)
      · by_cases hdc : (↑q : ℤ) ∣ c
        · exact absurd (two_to_three_b hda hdc) hdb
        · exact exactly_one_dvd_absurd p hp hp2 hq a b c heq ha hb hc hda hdb hdc
    · -- q ∣ b
      by_cases hda : (↑q : ℤ) ∣ a
      · exact descent hda hdb (two_to_three_c hda hdb)
      · by_cases hdc : (↑q : ℤ) ∣ c
        · exact absurd (two_to_three_a hdb hdc) hda
        · have heq' : b ^ p + a ^ p = c ^ p := by linarith
          exact exactly_one_dvd_absurd p hp hp2 hq b a c heq' hb ha hc hdb hda hdc
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
            hdc hqb' hda

end Fermat.SophieGermain
