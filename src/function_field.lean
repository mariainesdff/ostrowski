/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import field_theory.ratfunc
import ring_theory.dedekind_domain.adic_valuation
import basic

/-!
# Ostrowski's theorem for K(X)

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiF(T).pdf

## Tags
ring_norm, ostrowski
-/

noncomputable theory

open_locale polynomial

section infty

/-- The norm on K(X) associated to the place at infinity. -/
def ring_norm.infty (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ) (hc_pos : 0 < c)
  (hc_one_lt : 1 < c) : ring_norm (ratfunc K) :=
{ to_fun    := λ r, if r = 0 then 0 else c ^ r.int_degree,
  map_zero' := sorry,
  add_le'   := sorry,
  neg'      := λ r,
  begin
    by_cases r = 0,
    { simp only [h, neg_zero] } ,
    { have h₁ : ¬ -r = 0,
      { intro h₁,
        apply h,
        exact neg_eq_zero.1 h₁ },
      simp only [h, h₁, ratfunc.int_degree_neg] }
  end,
  eq_zero_of_map_eq_zero' := λ x hx,
  begin
    by_contra,
    simp only [h, if_false] at hx,
    linarith [zpow_eq_zero hx],
  end,
  mul_le'   := λ x y,
  begin
    by_cases x * y = 0,
    { simp only [h, eq_self_iff_true, if_true, ite_mul, mul_ite, mul_zero, zero_mul],
      rw mul_eq_zero at h,
      cases h,
      { simp only [h, eq_self_iff_true, if_true, if_t_t] },
      { simp only [h, eq_self_iff_true, if_true] } },
    { simp only [h, if_false, ite_mul, mul_ite, mul_zero, zero_mul],
      rw mul_eq_zero at h,
      rw not_or_distrib at h,
      cases h with h₁ h₂,
      simp only [h₁, h₂, if_false],
      rw ratfunc.int_degree_mul h₁ h₂,
      apply eq.le,
      repeat {rw ←real.rpow_int_cast},
      push_cast,
      exact real.rpow_add hc_pos _ _ }
  end }

@[simp] lemma ring_norm.infty_def (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ) 
  (hc_pos : 0 < c) (hc_one_lt : 1 < c) (r : ratfunc K):
    ring_norm.infty K c hc_pos hc_one_lt r = if r = 0 then 0 else c ^ r.int_degree := rfl

lemma ring_norm.infty_mul_eq (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ)
  (hc_pos : 0 < c) (hc_one_lt : 1 < c) :
  mul_eq (ring_norm.infty K c hc_pos hc_one_lt) :=
begin
  intros r s,
  simp only [ring_norm.infty_def, mul_eq_zero, ite_mul, mul_ite, mul_zero, zero_mul],
  by_cases r = 0 ∨ s = 0,
  { simp only [h, if_true],
    cases h,
    { simp only [h, eq_self_iff_true, if_true, if_t_t] },
    { simp only [h, eq_self_iff_true, if_true] } },
  { simp only [h, if_false],
    rw not_or_distrib at h,
    cases h with h₁ h₂,
    simp only [h₁, h₂, if_false],
    rw ratfunc.int_degree_mul h₁ h₂,
    repeat {rw ←real.rpow_int_cast},
    push_cast,
    exact real.rpow_add hc_pos _ _ }
end

lemma ring_norm.infty_is_nonarchimedean (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ)
  (hc_pos : 0 < c) (hc_one_lt : 1 < c) :
  is_nonarchimedean (ring_norm.infty K c hc_pos hc_one_lt) :=
begin
  intros r s,
  simp only [ring_norm.infty_def, le_max_iff],
  by_cases r + s = 0,
  { simp only [h, eq_self_iff_true, if_true],
    sorry},
  { simp only [h, if_false],
    by_cases h₁ : r = 0,
    { right,
      have h₂ : ¬ s = 0,
      { intro h₃,
        apply h,
        simp only [h₁, h₃, add_zero] },
      simp only [h₁, h₂, zero_add, if_false] },
    { have h₂ : ¬ s = 0 := sorry, -- this is false,
      simp only [h₁, h₂, if_false],

      sorry} }
end

end infty

/-- The maximal ideal on K[X] generated by an irreducible polynomial. -/
def polynomial.maximal_ideal_of_irreducible {K : Type*} [field K] [decidable_eq (ratfunc K)]
  {p : polynomial K} (hp : irreducible p) : is_dedekind_domain.height_one_spectrum (K[X]) :=
{ as_ideal := ideal.span({p}),
  is_prime := (ideal.span_singleton_prime (prime.ne_zero 
    (principal_ideal_ring.irreducible_iff_prime.mp hp))).mpr 
      (principal_ideal_ring.irreducible_iff_prime.mp hp),
  ne_bot   := by simp only [ne.def, ideal.span_singleton_eq_bot, 
    prime.ne_zero (principal_ideal_ring.irreducible_iff_prime.mp hp), not_false_iff] }

section adic

/-- The norm on K(X) associated to an irreducible polynomial. -/
def ring_norm.adic {K : Type*} [field K] [decidable_eq (ratfunc K)] (c : ℝ) (hc_pos : 0 < c)
  (hc_one_lt : 1 < c) {p : polynomial K} (hp : irreducible p) :
  ring_norm (ratfunc K) :=
{ to_fun    := λ r, if hr : r = 0 then 0 else c ^ multiplicative.to_add (with_zero.unzero
  ((@polynomial.maximal_ideal_of_irreducible K _ _ p hp).valuation.ne_zero_iff.mpr hr)),
  map_zero' := sorry,
  add_le'   := 
  begin
    intros r s,
    by_cases r + s = 0,
    { simp only [h, dif_pos],
      by_cases hr : r = 0,
      { have hs : s = 0,
        {sorry},
        simp only [hs, hr, dif_pos],
        linarith },
      { have hs : ¬ s = 0,
        {sorry},
        simp only [hs, hr, not_false_iff, dif_neg],
        exact add_nonneg (zpow_nonneg (le_of_lt hc_pos) _) 
          (zpow_nonneg (le_of_lt hc_pos) _) } },
    { simp only [h, not_false_iff, dif_neg],
      by_cases hr : r = 0,
      { have hs : ¬ s = 0,
        {sorry},
        simp only [hr, hs, not_false_iff, zero_add, dif_pos, dif_neg] },
      { by_cases hs : s = 0,
        {sorry},
        {sorry} } }
  end,
  neg'      := sorry,
  eq_zero_of_map_eq_zero' := 
  begin
    intros x hx,
    by_contra,
    simp only [h, not_false_iff, dif_neg] at hx,
    linarith [zpow_eq_zero hx]
  end,
  mul_le'   := sorry }

@[simp] lemma ring_norm.adic_def {K : Type*} [field K] [decidable_eq (ratfunc K)] 
  (c : ℝ) (hc_pos : 0 < c) (hc_one_lt : 1 < c) {p : polynomial K} (hp : irreducible p) 
    (r : ratfunc K): ring_norm.adic c hc_pos hc_one_lt hp r = if hr : r = 0 then 0 else 
      c ^ multiplicative.to_add (with_zero.unzero ((
        @polynomial.maximal_ideal_of_irreducible K _ _ p hp).valuation.ne_zero_iff.mpr hr)) 
:= rfl

lemma ring_norm.adic_mul_eq (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ)
  (hc_pos : 0 < c) (hc_one_lt : 1 < c) {p : polynomial K} (hp : irreducible p) :
  mul_eq (@ring_norm.adic K _ _ c hc_pos hc_one_lt p hp) :=
begin
  intros x y,
  simp only [mul_eq_zero, valuation.map_mul, ring_norm.adic_def],
  by_cases (x = 0 ∨ y = 0),
  {sorry},
  { rw not_or_distrib at h,
    simp only [h.1, h.2, or_self, not_false_iff, dif_neg],
    rw ←@zpow_add₀ _ _ c (by linarith),
    congr,
    rw ←to_add_mul,
    congr,
    rw ←with_zero.coe_inj,
    push_cast,
    repeat {rw with_zero.coe_unzero} }
end

lemma ring_norm.adic_is_nonarchimedean (K : Type*) [field K] [decidable_eq (ratfunc K)] (c : ℝ)
  (hc_pos : 0 < c) (hc_one_lt : 1 < c) {p : polynomial K} (hp : irreducible p) :
  is_nonarchimedean (@ring_norm.adic K _ _ c hc_pos hc_one_lt p hp) :=
begin
  intros x y,
  simp only [nonempty_of_inhabited, ring_norm.adic_def, le_max_iff],
  by_cases x + y = 0,
  {sorry},
  { simp only [h, not_false_iff, dif_neg],
    by_cases hx : x = 0,
    { have hy : ¬ y = 0,
      {sorry},
      simp only [hx, hy, not_false_iff, zero_add, dif_neg, le_refl, or_true] },
    { left,
      simp only [hx, not_false_iff, dif_neg],
      repeat {rw ←real.rpow_int_cast},
      apply real.rpow_le_rpow_of_exponent_le,
      { linarith },
      { norm_cast,
        simp only [multiplicative.to_add_le],
        
        sorry} } }
end

end adic

/- Ostrowski's Theorem 
theorem rat_ring_norm_p_adic_or_real (K : Type*) [field K] [decidable_eq (ratfunc K)]
  (c : ℝ) (hc_pos : 0 < c) (hc_one_lt : 1 < c) (f : ring_norm (ratfunc K))
  (hf_nontriv : f ≠ 1) (hf_triv_K : ∀ {x : K} (hx : x ≠ 0), f (ratfunc.C x) = 1)
  (hf_mul : mul_eq f) :
  (ring_norm.equiv f (ring_norm.infty K c hc_pos hc_one_lt)) ∨
  ∃ (p : K[X]) [hp : irreducible p],
    ring_norm.equiv f (@ring_norm.adic K _ _ c hc_pos hc_one_lt p hp) :=
begin
  sorry
end
-/