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
  map_zero' := by simp,
  add_le'   := 
    begin
      norm_cast,
      exact padic_norm.triangle_ineq,
    end,
  neg'      := by simp,
  eq_zero_of_map_eq_zero' := 
    begin
      norm_cast,
      intros x hx,
      exact padic_norm.zero_of_padic_norm_eq_zero hx,
    end,
  mul_le'   := 
    begin
      norm_cast,
      intros x y,
      rw padic_norm.mul,
    end }

lemma ring_norm.padic_mul_eq (p : ℕ) [hp : fact (nat.prime p)] :
  mul_eq (@ring_norm.padic p hp) :=
sorry

lemma ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : fact (nat.prime p)] :
  is_nonarchimedean (@ring_norm.padic p hp) :=
sorry

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
    linarith }
end
-- this isn't true if f = 0
-- use seminorm_one_eq_one_iff_ne_zero instead

lemma nat_norm_leq_one (n : ℕ) (heq : mul_eq f) (harc : is_nonarchimedean f) : f n ≤ 1 :=
begin
  induction n with c hc,
  simp,
  rw nat.succ_eq_add_one,
  specialize harc c 1,
  rw norm_one_eq_one _ heq at harc,
  simp,
  exact le_trans harc (max_le hc rfl.ge)
end

/-- Ostrowski's Theorem -/
theorem rat_ring_norm_p_adic_or_real (f : ring_norm ℚ) (hf_nontriv : f ≠ 1) (hf_mul : mul_eq f) :
  (ring_norm.equiv f ring_norm.real) ∨
  ∃ (p : ℕ) [hp : fact (nat.prime p)], ring_norm.equiv f (@ring_norm.padic p hp) :=
begin
    by_cases bdd : ∀ z : ℤ, f z ≤ 1,
    { sorry /- p-adic case -/ },
    { sorry /- Euclidean case -/ }
end