/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import number_theory.padics.padic_norm
import basic

/-!
# Ostrowski's theorem for ℚ

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

noncomputable theory

section real

/-- The usual absolute value on ℚ. -/
def ring_norm.real : ring_norm ℚ :=
{ to_fun    := λ x : ℚ, |x|,
  map_zero' := by simp only [rat.cast_zero, abs_zero],
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  eq_zero_of_map_eq_zero' := 
  by simp only [abs_eq_zero, rat.cast_eq_zero, imp_self, forall_const],
  mul_le'   := norm_mul_le }

@[simp] lemma ring_norm_eq_abs (r : ℚ) : ring_norm.real r = |r| := rfl

lemma ring_norm.real_mul_eq : mul_eq ring_norm.real :=
by simp only [mul_eq_def, abs_mul, ring_norm_eq_abs, rat.cast_mul, eq_self_iff_true, forall_const]

end real

section padic

/-- The p-adic norm on ℚ. -/
def ring_norm.padic (p : ℕ) [hp : fact (nat.prime p)] : ring_norm ℚ :=
{ to_fun    := λ x : ℚ, (padic_norm p x: ℝ),
  map_zero' := by simp only [padic_norm.zero, rat.cast_zero],
  add_le'   := by norm_cast; exact padic_norm.triangle_ineq,
  neg'      := by simp only [padic_norm.neg, eq_self_iff_true, forall_const],
  eq_zero_of_map_eq_zero' := by norm_cast; exact @padic_norm.zero_of_padic_norm_eq_zero p _,
  mul_le'   := by simp only [padic_norm.mul, le_refl, forall_const, rat.cast_mul], }

@[simp] lemma ring_norm_eq_padic_norm (p : ℕ) [hp : fact (nat.prime p)] (r : ℚ) :
  ring_norm.padic p r = padic_norm p r := rfl

lemma ring_norm.padic_mul_eq (p : ℕ) [hp : fact (nat.prime p)] :
  mul_eq (@ring_norm.padic p hp) :=
by simp only [mul_eq_def, ring_norm_eq_padic_norm, padic_norm.mul, rat.cast_mul,
  eq_self_iff_true, forall_const]

lemma ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : fact (nat.prime p)] :
  is_nonarchimedean (@ring_norm.padic p hp) :=
begin
  simp only [is_nonarchimedean_def, ring_norm_eq_padic_norm],
  norm_cast,
  exact @padic_norm.nonarchimedean p _,
end

end padic

variables (f : ring_norm ℚ)

lemma norm_one_eq_one (h : mul_eq f) : f 1 = 1 := 
begin
  have H₁ : (f 1)*(f 1) = f 1,
  calc
    (f 1)*(f 1) = f (1 * 1) : by rw ←h 1 1
    ... = f 1 : by norm_num,
  have H₂ : f 1 ≠ 0,
  { intro f10,
    have : (1 : ℚ) = 0 := f.eq_zero_of_map_eq_zero' 1 f10,
    linarith },
    calc f 1 = (f 1) * (f 1) * (f 1)⁻¹ : by field_simp
    ... = (f 1) * (f 1)⁻¹ : by rw H₁
    ... = 1 : by field_simp,
end

section non_archimedean

lemma nat_norm_leq_one (n : ℕ) (heq : mul_eq f) (harc : is_nonarchimedean f) : f n ≤ 1 :=
begin
  induction n with c hc,
  { simp only [nat.cast_zero, map_zero, zero_le_one], },
  { rw nat.succ_eq_add_one,
    specialize harc c 1,
    rw norm_one_eq_one _ heq at harc,
    simp only [nat.cast_add, nat.cast_one],
    exact le_trans harc (max_le hc rfl.ge), },
end

lemma int_norm_le_one (n : ℤ) (heq : mul_eq f) (harc : is_nonarchimedean f) : f n ≤ 1 :=
sorry
-- Proof strategy:

-- Prove nontrivial on ℚ implies nontrivial on ℕ
lemma nat_nontriv_of_rat_nontriv (hf_mul : mul_eq f) : f ≠ 1 → (∃ n : ℕ, f n < 1) := sorry

-- Show that there is a prime with norm < 1
lemma ex_prime_norm_lt_one (heq : mul_eq f) (harc : is_nonarchimedean f) : 
  ∃ (p : ℕ) [hp : fact (nat.prime p)], f p < 1 := sorry

-- Show that I is an ideal
def I (harc : is_nonarchimedean f) (heq : mul_eq f) : ideal ℤ := 
{ carrier := {a : ℤ | f a < 1},
  add_mem' := begin
     intros a b ha hb,
     simp,
     have : max (f a) (f b) < 1 := max_lt ha hb,
     linarith [harc a b]
  end,
  zero_mem' := begin
    change f 0 < 1,
    rw [map_zero f],
    exact zero_lt_one,
  end,
  smul_mem' := begin
    intros a b hb,
    change f (↑(a * b)) < 1,
    simp,
    rw heq,
    exact mul_lt_of_le_of_lt_one' (int_norm_le_one _ _ heq harc) hb (map_nonneg f b) zero_lt_one,
  end }

-- Show that it's equal to pℤ
-- Get s
-- Finish

end non_archimedean

section archimedean

end archimedean

/-- Ostrowski's Theorem -/
theorem rat_ring_norm_p_adic_or_real (f : ring_norm ℚ) (hf_nontriv : f ≠ 1) (hf_mul : mul_eq f) :
  (ring_norm.equiv f ring_norm.real) ∨
  ∃ (p : ℕ) [hp : fact (nat.prime p)], ring_norm.equiv f (@ring_norm.padic p hp) :=
begin
    by_cases bdd : ∀ z : ℤ, f z ≤ 1,
    { sorry /- p-adic case -/ },
    { sorry /- Euclidean case -/ }
end