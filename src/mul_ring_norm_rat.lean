import number_theory.padics.padic_norm
import basic
import order.filter.basic
import analysis.special_functions.log.base
import analysis.normed.ring.seminorm
import data.nat.digits

open_locale big_operators

/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas about mul_ring_norm ℚ

-/

noncomputable theory

variable {f : mul_ring_norm ℚ}

-- TODO: remove this
-- I think this is a missing lemma in mathlib and maybe we can use this for now.
-- (Done)
lemma f_mul_eq : mul_eq f := f.map_mul'

-- The norm of -1 is 1
-- (Done)
lemma norm_neg_one_eq_one : f (-1) = 1 :=
begin
  have H₁ : f (-1) * f (-1) = 1,
  calc
    f (-1) * f (-1)  = f ((-1) * (-1)) : by simp
    ... = f 1 : by norm_num
    ... = 1 : f.map_one',
  have H₂: f (-1) ≥ 0 := map_nonneg f (-1),
  rw mul_self_eq_one_iff at H₁,
  cases H₁,
  { exact H₁ },
  { rw H₁ at H₂,
    have h' : ¬(-1 ≥ (0 : ℝ)) := by norm_num,
    contradiction },
end

-- If x is non-zero, then the norm of x is larger than zero.
-- (Done)
lemma norm_pos_of_ne_zero {x : ℚ} (h : x ≠ 0) : f x > 0 :=
lt_of_le_of_ne (map_nonneg f x) (λ h', h (f.eq_zero_of_map_eq_zero' x h'.symm))

--TODO: generalise to division rings, get rid of field_simp
-- (Done)
lemma ring_norm.div_eq (p : ℚ) {q : ℚ} (hq : q ≠ 0) : f (p / q) = (f p) / (f q) :=
begin
  have H : f q ≠ 0,
  { intro fq0,
    have := f.eq_zero_of_map_eq_zero' q fq0,
    exact hq this },
  calc f (p / q) = f (p / q) * f q / f q : by field_simp
  ... = f (p / q * q)  / f q : by simp
  ... = f p / f q : by field_simp,
end

-- This lemma look a bit strange to me.
-- (Done)
lemma int_norm_bound_iff_nat_norm_bound :
  (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1) :=
begin
  split,
  { intros h z,
    obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
    { exact h n },
    { have : ↑((-1 : ℤ) * n) = (-1 : ℚ) * n := by norm_cast,
      rw [neg_eq_neg_one_mul, this, f_mul_eq, norm_neg_one_eq_one, one_mul],
      exact h n } },
  { intros h n,
    exact_mod_cast (h n) },
end

-- (Done)
lemma mul_eq_pow {a : ℚ} {n : ℕ} : f (a ^ n) = (f a) ^ n :=
begin
  induction n with d hd,
  simp only [pow_zero],
  exact f.map_one',
  rw [pow_succ, pow_succ, ←hd, f_mul_eq],
end