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

variables {f : ring_norm ℚ}

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

lemma norm_neg_one_eq_one (h : mul_eq f) : f (-1) = 1 :=
begin
  have H₁ : f (-1) * f (-1) = 1,
  calc
    f (-1) * f (-1)  = f ((-1) * (-1)) : by rw ←h (-1) (-1)
    ... = f 1 : by norm_num
    ... = 1 : norm_one_eq_one h,
  have H₂: f (-1) ≥ 0 := map_nonneg f (-1),
  rw mul_self_eq_one_iff at H₁,
  cases H₁,
  { exact H₁ },
  { rw H₁ at H₂,
    have h' : ¬(-1 ≥ (0 : ℝ)) := by norm_num,
    contradiction },
end

--TODO: generalise to division rings, get rid of field_simp
lemma ring_norm.div_eq (h : mul_eq f) (p : ℚ) {q : ℚ} (hq : q ≠ 0) : f (p / q) = (f p) / (f q) :=
begin
  have H : f q ≠ 0,
  { intro fq0,
    have := f.eq_zero_of_map_eq_zero' q fq0,
    exact hq this },
  calc f (p / q) = f (p / q) * f q / f q : by field_simp
  ... = f (p / q * q)  / f q : by rw h (p / q) q
  ... = f p / f q : by field_simp,
end

section non_archimedean

lemma nat_norm_leq_one (n : ℕ) (heq : mul_eq f) (harc : is_nonarchimedean f) : f n ≤ 1 :=
begin
  induction n with c hc,
  { simp only [nat.cast_zero, map_zero, zero_le_one], },
  { rw nat.succ_eq_add_one,
    specialize harc c 1,
    rw norm_one_eq_one heq at harc,
    simp only [nat.cast_add, nat.cast_one],
    exact le_trans harc (max_le hc rfl.ge), },
end

lemma int_norm_le_one (z : ℤ) (heq : mul_eq f) (harc : is_nonarchimedean f) : f z ≤ 1 :=
begin
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
  { exact nat_norm_leq_one n heq harc },
  { have : ↑((-1 : ℤ) * n) = (-1 : ℚ) * n := by norm_cast,
    rw [neg_eq_neg_one_mul, this, heq, norm_neg_one_eq_one heq, one_mul],
    exact nat_norm_leq_one n heq harc,
  },
end
-- Proof strategy:

-- Prove nontrivial on ℚ implies nontrivial on ℕ
lemma nat_nontriv_of_rat_nontriv (hf_mul : mul_eq f) (harc : is_nonarchimedean f) : f ≠ 1 → (∃ n : ℕ, n ≠ 0 ∧ f n < 1) := 
begin
  contrapose!,
  intro hfnge1,
  have hfnateq1 : ∀ n : ℕ, n ≠ 0 → f n = 1,
  { intros n hnneq0,
    specialize hfnge1 n hnneq0,
    have := nat_norm_leq_one n hf_mul harc,
    linarith },
  ext,
  by_cases h : x = 0,
  { simp only [h, map_zero]},
  { simp only [h, ring_norm.apply_one, if_false],
    rw ← rat.num_div_denom x,
    have hdenomnon0 : (x.denom : ℚ) ≠ 0,
    { norm_cast,
      linarith [x.pos] }, --probably rw on x.pos
    rw ring_norm.div_eq hf_mul (x.num : ℚ) hdenomnon0,
    have H₁ : f x.num = 1,
    { have pos_num_f_eq_1 : ∀ a : ℚ , (a.num > 0 → f a.num = 1),
      { intros a num_pos,
        have coe_eq : (a.num : ℚ) = (a.num.to_nat : ℚ),
      { norm_cast,
        exact (int.to_nat_of_nonneg (by linarith)).symm, },
      rw coe_eq,
      /-have x_num_pos : x.num > 0,
      { apply lt_of_le_of_ne hsign,
        intro H,
        apply h,
        rw rat.zero_iff_num_zero,
        rw H },-/
      have a_num_nat_nonzero : a.num.to_nat ≠ 0,
      { intro H,
        rw int.to_nat_eq_zero at H,
        linarith },
      exact hfnateq1 _ a_num_nat_nonzero },
      by_cases hsign : x.num ≥ 0,
      { apply pos_num_f_eq_1,
        rw [rat.zero_iff_num_zero, ←ne.def] at h,
        exact lt_of_le_of_ne hsign h.symm },
      { push_neg at hsign,
        rw ←f.to_fun_eq_coe,
        rw ←f.neg' x.num,
        rw f.to_fun_eq_coe,
        norm_cast,
        rw ←rat.num_neg_eq_neg_num,
        apply pos_num_f_eq_1, 
        rw rat.num_neg_eq_neg_num,
        exact neg_pos.mpr hsign} },
    have H₂ : f x.denom = 1,
    { have := x.pos,
      rw pos_iff_ne_zero at this,
      exact hfnateq1 x.denom this },
    rw [H₁, H₂],
    norm_num }
end

def ring_norm.to_monoid_hom (f : ring_norm ℚ) (hf : mul_eq f) : monoid_hom ℚ ℝ :=
{ to_fun   := f,
  map_one' := norm_one_eq_one hf,
  map_mul' := hf }

-- Show that there is a prime with norm < 1
lemma ex_prime_norm_lt_one (heq : mul_eq f) (harc : is_nonarchimedean f) 
  (h : f ≠ 1) : ∃ (p : ℕ) [hp : fact (nat.prime p)], f p < 1 :=
begin
  by_contra',
  obtain ⟨n, hn1, hn2⟩ := nat_nontriv_of_rat_nontriv heq harc h,
  let t := nat.factors n,
  rw ← nat.prod_factors hn1 at hn2,
  have exp : ∀ q : ℕ, q ∈ nat.factors n → 1 ≤ f q,
  { sorry },
  simp only [nat.cast_list_prod] at hn2,
  have hf_mh: f.to_fun = (f.to_monoid_hom heq).to_fun := rfl,
  rw [← f.to_fun_eq_coe, hf_mh, (f.to_monoid_hom heq).to_fun_eq_coe, map_list_prod] at hn2,
  
  sorry
end

-- Show that 𝔞 is an ideal
def 𝔞 (harc : is_nonarchimedean f) (heq : mul_eq f) : ideal ℤ :=
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
    exact mul_lt_of_le_of_lt_one' (int_norm_le_one a heq harc) hb (map_nonneg f b) zero_lt_one,
  end }

-- Show that it contains pZ
lemma a_contains_prime_ideal (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc heq ≥ ideal.span {p} :=
begin
  obtain ⟨p, hp, hbound⟩ := ex_prime_norm_lt_one heq harc h_nontriv,
  use p,
  split,
  { exact hp },
  sorry,
end

-- Show that it's in fact equal to pZ (since pZ is a maximal ideal)
lemma a_eq_prime_ideal (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc heq = ideal.span {p} :=
begin
  obtain ⟨p, hp, hinc⟩ := a_contains_prime_ideal harc heq h_nontriv,
  use p,
  split, { exact hp },
  cases hp,
  have hp' := nat.prime_iff.mp hp,
  rw ←ideal.span_singleton_prime (nat.prime.ne_zero hp) at hp',
  sorry,
end

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