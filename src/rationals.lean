/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import number_theory.padics.padic_norm
import basic
import order.filter.basic
import analysis.special_functions.log.base
import analysis.normed.ring.seminorm
import data.nat.digits
import mul_ring_norm_rat
import nonarchimedean
import ring_theory.power_series.basic
import analysis.specific_limits.normed
import topology.algebra.order.basic

open_locale big_operators

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
def mul_ring_norm.real : mul_ring_norm ℚ :=
{ to_fun    := λ x : ℚ, |x|,
  map_zero' := by simp only [rat.cast_zero, abs_zero],
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  eq_zero_of_map_eq_zero' := 
  by simp only [abs_eq_zero, rat.cast_eq_zero, imp_self, forall_const],
  map_one' := by simp only [algebra_map.coe_one, abs_one],
  map_mul' := by exact_mod_cast abs_mul,
}

@[simp] lemma mul_ring_norm_eq_abs (r : ℚ) : mul_ring_norm.real r = |r| := rfl

end real

section padic

/-- The p-adic norm on ℚ. -/
def mul_ring_norm.padic (p : ℕ) [hp : fact (nat.prime p)] : mul_ring_norm ℚ :=
{ to_fun    := λ x : ℚ, (padic_norm p x: ℝ),
  map_zero' := by simp only [padic_norm.zero, rat.cast_zero],
  add_le'   := by norm_cast; exact padic_norm.triangle_ineq,
  neg'      := by simp only [padic_norm.neg, eq_self_iff_true, forall_const],
  eq_zero_of_map_eq_zero' := by norm_cast; exact @padic_norm.zero_of_padic_norm_eq_zero p _,
  map_one' := by exact_mod_cast padic_norm.one,
  map_mul' := by simp only [padic_norm.mul, rat.cast_mul, eq_self_iff_true, forall_const],
}

@[simp] lemma mul_ring_norm_eq_padic_norm (p : ℕ) [hp : fact (nat.prime p)] (r : ℚ) :
  mul_ring_norm.padic p r = padic_norm p r := rfl

lemma mul_ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : fact (nat.prime p)] :
  is_nonarchimedean (@mul_ring_norm.padic p hp) :=
begin
  simp only [is_nonarchimedean_def, mul_ring_norm_eq_padic_norm],
  exact_mod_cast @padic_norm.nonarchimedean p _
end

end padic

variable {f : mul_ring_norm ℚ}

-- This lemma is missing in the mathlib I think.
lemma mul_ring_norm.neg {R : Type*} [non_assoc_ring R] {f : mul_ring_norm R} 
  (a : R) : f (-a) = f a := f.neg' a

section non_archimedean

-- Show that 𝔞 is an ideal
-- Maybe this should be inserted into the final proof.
def 𝔞 (harc : is_nonarchimedean f) : ideal ℤ :=
{ carrier := {a : ℤ | f a < 1},
  add_mem' := λ a b ha hb, by simp only [set.mem_set_of_eq, int.cast_add] at ha hb ⊢;
    linarith [(harc a b), (max_lt ha hb)],
  zero_mem' := by simp only [set.mem_set_of_eq, algebra_map.coe_zero, map_zero, zero_lt_one],
  smul_mem' := λ a b hb, by simp only [algebra.id.smul_eq_mul, set.mem_set_of_eq, int.cast_mul,
    map_mul, mul_lt_of_le_of_lt_one' (int_norm_le_one a harc) hb (map_nonneg f b) zero_lt_one]}

--Maybe this should be inserted into the final proof.
lemma a_proper (harc : is_nonarchimedean f) : 𝔞 harc ≠ (⊤ : ideal ℤ) :=
begin
  rw ideal.ne_top_iff_one,
  dsimp only [𝔞, submodule.mem_mk, set.mem_set_of_eq, int.cast_one, not_lt],
  simp only [algebra_map.coe_one, map_one, lt_self_iff_false, not_false_iff],
end

-- Show that it contains pZ
-- Maybe this should be inserted into the final proof.
lemma a_contains_prime_ideal (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc ≥ ideal.span {p} :=
begin
  obtain ⟨p, hp, hbound⟩ := ex_prime_norm_lt_one harc h_nontriv,
  refine ⟨p, hp, _⟩,
  { apply ideal.span_le.mpr,
    simp only [set.singleton_subset_iff, set_like.mem_coe],
    exact hbound, }
end

-- Show that it's in fact equal to pZ (since pZ is a maximal ideal)
-- Maybe this should be inserted into the final proof.
lemma a_eq_prime_ideal (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc = ideal.span {p} :=
by obtain ⟨p, hp, hinc⟩ := a_contains_prime_ideal harc h_nontriv;
  refine ⟨p, hp, ((principal_ideal_ring.is_maximal_of_irreducible
    (nat.prime_iff_prime_int.mp hp.1).irreducible).eq_of_le (a_proper harc) hinc).symm⟩

-- I will try to see whether there is a similar version of this (hopefully)
lemma mult_finite {a : ℤ} {p : ℕ} (hp : nat.prime p) (ha : a ≠ 0) :
  multiplicity.finite (p : ℤ) a :=
by apply multiplicity.finite_int_iff.mpr;
  simp only [ha, hp.ne_one, int.nat_abs_of_nat, ne.def, not_false_iff, and_self]

-- the equality at the end of the next lemma
lemma rearrange {p v : ℝ} (m : ℕ) (hp : p > 0) (hlogp : real.log p ≠ 0) (hv : v > 0) : 
  v ^ m = (p ^ m)⁻¹ ^ (-real.log v / real.log p) :=
begin
  have : p ^ m = p ^ (m : ℝ) := by norm_cast,
  rw [←real.rpow_neg_one, this, ←(real.rpow_mul (le_of_lt hp)), 
    ←(real.rpow_mul (le_of_lt hp)), neg_div, mul_neg, mul_neg, mul_one, neg_mul, neg_neg,
      mul_div, ←real.log_rpow hv, real.rpow_def_of_pos hp, mul_div_left_comm,
        div_self hlogp, mul_one, real.exp_log],
  { norm_cast },
  { norm_cast,
    exact pow_pos hv m }
end

-- f a = (f p)^m = ring_norm a
lemma int_val_eq (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)] (s : ℝ) [hs : s > 0],
    ∀ (a : ℤ), f a = (@mul_ring_norm.padic p hp a)^s :=
begin
  obtain ⟨p, hp, h_aeq⟩ := a_eq_prime_ideal harc h_nontriv,
  refine ⟨p, hp, _⟩,
  cases hp,
  have fpgt0 := @norm_pos_of_ne_zero f _ (nat.cast_ne_zero.mpr (ne_of_gt hp.pos)),
  let s := (-real.log (f p : ℝ) / real.log p),
  have hs : s > 0,
  { refine div_pos _ (@real.log_pos p (by exact_mod_cast hp.one_lt)),
    { refine neg_pos.mpr ((real.log_neg_iff fpgt0).mpr _),
      have p_mem_a : (p : ℤ) ∈ ideal.span ({p} : set ℤ) := by rw ideal.mem_span_singleton,
      rw ←h_aeq at p_mem_a,
      exact p_mem_a, } },
  refine ⟨s, hs, _⟩,
  intro a,
  by_cases ha : a = 0,
  { simp_rw [ha, int.cast_zero, map_zero],
    exact (real.zero_rpow (norm_num.ne_zero_of_pos s hs)).symm },
  obtain ⟨b, hapb, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd (mult_finite hp ha),
  let m := (multiplicity (p : ℤ) a).get (mult_finite hp ha),
  have : f a = (f p) ^ m,
  { rw hapb,
    have hb : ↑b ∉ 𝔞 harc,
    { rw h_aeq,
      intro hmem,
      rw ideal.mem_span_singleton' at hmem,
      obtain ⟨k, hk⟩ := hmem,
      apply hndiv,
      rw dvd_iff_exists_eq_mul_left,
      refine ⟨k, hk.symm⟩ },
    dsimp only [𝔞] at hb,
    simp only [int.cast_id, submodule.mem_mk, set.mem_set_of_eq, not_lt] at hb,
    suffices h'' : f ((p : ℚ) ^ m * (b : ℚ)) = (f (p : ℚ)) ^ m,
    { convert h'',
      norm_cast },
    rw [f_mul_eq, le_antisymm (int_norm_le_one b harc) hb, mul_one, mul_eq_pow] },
  rw this,
  simp only [mul_ring_norm_eq_padic_norm, ha, padic_norm.eq_zpow_of_nonzero, ne.def,
    int.cast_eq_zero, not_false_iff, padic_val_rat.of_int, zpow_neg, zpow_coe_nat,
      rat.cast_inv, rat.cast_pow, rat.cast_coe_nat],
  unfold padic_val_int padic_val_nat,
  simp [ha, hp.ne_one, int.nat_abs_pos_of_ne_zero ha, multiplicity.int.nat_abs p a],
  have hppos : (p : ℝ) > 0 := nat.cast_pos.mpr (hp.pos),
  exact rearrange m hppos (norm_num.ne_zero_of_pos _ (@real.log_pos p (by exact_mod_cast hp.one_lt))) fpgt0,
end

lemma cast_pow_sub (r : ℝ) (a b : ℤ) : r ^ (a - b) = r ^ ((a : ℝ) - (b : ℝ)) := by norm_cast

lemma cast_pow (r : ℝ) (a : ℕ) : r ^ a = r ^ (a : ℝ) := by norm_cast

-- Extend this to ℚ using div_eq
lemma rat_val_eq (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)] (s : ℝ) (hs : s > 0),
    ∀ (a : ℚ), f a = (@mul_ring_norm.padic p hp a)^s :=
begin
  obtain ⟨p, hp, s, hs, h_int⟩ := int_val_eq harc h_nontriv,
  use [p, hp, s, hs],
  intro a,
  by_cases ha : a = 0,
  { rw [ha, map_zero, map_zero],
    have hs' : s ≠ 0 := norm_num.ne_zero_of_pos s hs,
    exact (real.zero_rpow hs').symm },
  have hcast : f (a.denom) = (@mul_ring_norm.padic p hp a.denom) ^ s := h_int a.denom,
  rw [←rat.num_div_denom a, ring_norm.div_eq, h_int, hcast],
  simp [ha],
  unfold padic_val_rat,
  rw [cast_pow_sub, real.rpow_sub],
  unfold padic_norm,
  simp [rat.num_ne_zero_of_ne_zero ha, rat.denom_ne_zero a],
  rw [real.inv_rpow, real.inv_rpow],
  simp only [inv_div_inv],
  rw ←real.div_rpow,
  repeat {
    -- fact hp --> hp
    cases hp,
    rw cast_pow,
    exact real.rpow_nonneg_of_nonneg (le_of_lt (nat.cast_pos.mpr hp.pos)) _
  },
  cases hp,
  exact (nat.cast_pos.mpr hp.pos),
  norm_cast,
  exact rat.denom_ne_zero a,
end

-- Finish: hence f and padic are equivalent
lemma f_equiv_padic (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) : 
 ∃ (p : ℕ) [hp : fact (nat.prime p)], mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) :=
begin
  obtain ⟨p, hp, s, hs, h⟩ := rat_val_eq harc h_nontriv,
  use [p, hp, 1 / s],
  refine ⟨one_div_pos.mpr hs, _⟩,
  ext a,
  rw [h, ←real.rpow_mul],
  simp [norm_num.ne_zero_of_pos s hs],
  unfold mul_ring_norm.padic,
  simp only [map_nonneg]
end

end non_archimedean

section archimedean
--Sum inequality
lemma Sum_le (n : ℕ) (ι : ℕ → ℚ) : f (∑ i in finset.range n, ι i) ≤ ∑ i in finset.range n, f (ι i) :=
begin
  induction n with n hn,
  { simp only [finset.range_zero, finset.sum_empty, map_zero] },
  { rw finset.sum_range_succ,
    rw finset.sum_range_succ,
    calc f (∑ (x : ℕ) in finset.range n, ι x + ι n)
        ≤ f (∑ i in finset.range n, ι i) + f (ι n) : f.add_le' _ _
    ... ≤ (∑ i in finset.range n, f (ι i)) + f (ι n) : add_le_add_right hn _ }
end

-- This should be the same as `Sum_le`
lemma Sum_le' (n : ℕ) (ι : finset.Iio n → ℚ) :
  f (∑ i : finset.Iio n, ι i) ≤ ∑ i : finset.Iio n, f (ι i) := sorry

--First limit
lemma limit1 {N : ℝ} (hN : 0 < N) : filter.tendsto (λ n : ℕ, N ^ (1 / (n : ℝ))) filter.at_top (nhds 1) :=
begin
  rw ←real.exp_log hN,
  simp_rw [←real.exp_mul],
  refine real.tendsto_exp_nhds_0_nhds_1.comp _,
  simp_rw [mul_one_div],
  apply tendsto_const_div_at_top_nhds_0_nat
end

--Second limit
lemma limit2 {c : ℝ} (hc : 0 < c) : filter.tendsto (λ n : ℕ, (1 + (n : ℝ)*c)^(1 / (n : ℝ))) filter.at_top (nhds 1) :=
begin
  have cne0 : c ≠ 0 := ne_of_gt hc, 
  have : (λ n : ℕ, (1+(n : ℝ)*c)^(1 / (n : ℝ))) = (λ (x : ℝ), x ^ (1 / ((1 / c) * x  + (- 1) / c))) ∘ (λ y : ℝ, 1 + c*y) ∘ coe,
  { ext n, simp, rw mul_add, rw ←mul_assoc, simp, rw div_eq_mul_inv, rw add_comm c⁻¹, rw add_assoc, rw [neg_mul, one_mul, add_right_neg, add_zero, inv_mul_cancel cne0, one_mul, mul_comm] },
  rw this,
  have : 1 / c ≠ 0 := one_div_ne_zero cne0,
  refine (tendsto_rpow_div_mul_add 1 (1 / c) (-1 / c) this.symm).comp _,
  have : filter.tendsto (λ y : ℝ, 1 + c*y) filter.at_top filter.at_top,
  { apply filter.tendsto_at_top_add_const_left,
    apply filter.tendsto.const_mul_at_top hc,
    intros x hx,
    exact hx },
  exact this.comp tendsto_coe_nat_at_top_at_top
end

--Potentially useful
example {c : ℝ} (hc : 0 < c) : filter.tendsto (λ n : ℕ, ((n : ℝ))^(1 / (n : ℝ))) filter.at_top (nhds 1) :=
begin
  have hf : (λ n : ℕ, (n : ℝ)^(1 / (n : ℝ))) = λ n : ℕ, (((λ x : ℝ, x^(1 / x)) ∘ coe) n),
  { ext, simp only [eq_self_iff_true] },
  rw hf,
  apply filter.tendsto.comp _ tendsto_coe_nat_at_top_at_top,
  exact tendsto_rpow_div,
  apply_instance,
end

lemma pow_mul_pow_le_max_pow {a b : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a^m * b^n ≤ max a b ^ (m + n) :=
begin
  rw pow_add,
  apply mul_le_mul,
  { exact pow_le_pow_of_le_left ha (le_max_left a b) m },
  { exact pow_le_pow_of_le_left hb (le_max_right a b) n },
  { exact pow_nonneg hb n },
  { apply pow_nonneg,
    rw le_max_iff,
    left,
    exact ha }
end 

lemma inter_ineq {n : ℕ} (x y : ℚ) (hf : ∀ m : ℕ, f m ≤ 1) : f (x + y)^(n : ℝ) ≤ (n + 1 : ℝ) * max (f x) (f y)^n :=
begin
  norm_cast,
  rw [←mul_eq_pow, add_pow],
  apply le_trans (Sum_le (n + 1) _),
  suffices goal_1 : ∑ i in finset.range (n + 1), f ( x^i * y^(n - i) * (n.choose i) )
    = ∑ i in finset.range (n + 1), f (x ^ i) * f(y ^ (n - i)) * f (n.choose i),
  { rw goal_1,
    clear goal_1,
    calc ∑ i in finset.range (n + 1), f (x ^ i) * f(y ^ (n - i)) * f (n.choose i)
        ≤ ∑ i in finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) : 
          begin
            apply finset.sum_le_sum,
            intros i hi,
            conv { to_rhs, rw ←mul_one (f (x ^ i) * f (y ^ (n - i))) },
            exact mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (map_nonneg f _) (map_nonneg f _))
          end
    ... ≤ ∑ i in finset.range (n + 1), max (f x) (f y) ^ n : 
          begin
            apply finset.sum_le_sum,
            intros i hi,
            have : i + (n - i) = n,
            { rw add_comm,
              apply nat.sub_add_cancel,
              simp at hi,
              linarith },
            conv { to_rhs, rw ←this },
            repeat { rw mul_eq_pow },
            exact pow_mul_pow_le_max_pow (map_nonneg f x) (map_nonneg f y),
          end
    ... = ↑(n + 1) * max (f x) (f y) ^ n : by simp, },
    { congr',
      ext,
      rw [f_mul_eq, f_mul_eq] }
end

lemma root_ineq {n : ℕ} (x y : ℚ) (hn : n ≠ 0) (hf : ∀ m : ℕ, f m ≤ 1) : f (x + y) ≤ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y) :=
begin
  refine le_of_pow_le_pow n _ (nat.pos_of_ne_zero hn) _,
  { apply mul_nonneg,
    { apply real.rpow_nonneg_of_nonneg,
      norm_cast,
      linarith },
    { rw le_max_iff,
      left,
      exact map_nonneg f x } },
  { rw mul_pow,
    have : 0 ≤ (n : ℝ) + 1 := by { norm_cast, linarith },
    nth_rewrite 1 [←real.rpow_nat_cast],
    rw [←real.rpow_mul this, one_div],
    have : (n : ℝ) ≠ 0 := by { norm_cast, exact hn },
    rw [inv_mul_cancel this, real.rpow_one, ←real.rpow_nat_cast],
    exact inter_ineq x y hf }
end

-- A norm is non-archimedean iff it's bounded on the naturals
lemma non_archimedean_iff_nat_norm_bound : (∀ n : ℕ, f n ≤ 1) ↔ is_nonarchimedean f :=
begin
  split,
  { intros H x y,
    have lim : filter.tendsto (λ n : ℕ, (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y)) filter.at_top (nhds (max (f x) (f y))),
    { nth_rewrite 0 ←one_mul (max (f x) (f y)),
      apply filter.tendsto.mul_const (max (f x) (f y)),
      suffices goal_1 : (λ k : ℕ, ((k : ℝ) + 1) ^ (1 / (k : ℝ))) = (λ k : ℕ, (1 + (k : ℝ) * 1) ^ (1 / (k : ℝ))),
      { rw goal_1,
        clear goal_1,
        exact limit2 (real.zero_lt_one) },
      { ext k,
        simp,
        rw add_comm } },
    apply ge_of_tendsto lim _,
    simp only [filter.eventually_at_top, ge_iff_le],
    use 1,
    intros b hb, 
    have : b ≠ 0 := nat.one_le_iff_ne_zero.mp hb,
    exact root_ineq x y this H },
  { intros hf n,
    exact nat_norm_le_one n hf }
end

lemma aux1 {n₀ : ℕ} (hf : ∃ n : ℕ, 1 < f n) (dn₀ : n₀ = nat.find hf) : 1 < n₀ :=
begin
  have hn₀ := nat.find_spec hf,
  rw ←dn₀ at hn₀,
  by_contra',
  rw lt_iff_not_ge at hn₀,
  interval_cases n₀,
  { apply hn₀,
    simp only [nat.cast_zero, map_zero, ge_iff_le, zero_le_one] },
  { apply hn₀,
    simp [f.map_one'] }
end

lemma list.map_with_index_append' {α M : Type*} [add_comm_monoid M] 
  (K L : list α) (f : ℕ → α → M) : 
  (K ++ L).map_with_index f = K.map_with_index f ++ L.map_with_index (λ i a, f (i + K.length) a) :=
begin
  induction K with a J IH generalizing f,
  { simp },
  { simp [IH (λ i, f (i+1)), add_assoc], }
end

-- This should be the same as `list.map_with_index_sum_to_finset_sum`
lemma list.map_with_index_sum_to_finset_sum' {β A : Type*} [add_comm_monoid A] {f : ℕ → β → A} 
  {L : list β}  [inhabited β] : (L.map_with_index f).sum = ∑ i : finset.Iio L.length, 
    f i ((L.nth_le i (finset.mem_Iio.1 i.2))) :=
begin
  sorry
end

lemma list.map_with_index_sum_to_finset_sum {β A : Type*} [add_comm_monoid A] {f : ℕ → β → A} 
  {L : list β}  [inhabited β] : (L.map_with_index f).sum = ∑ i in finset.range L.length, 
    f i ((L.nth i).get_or_else default) :=
begin
  apply list.reverse_rec_on L, -- the induction principle which works best
  { simp, },
  { intros M a IH,
    simp [list.map_with_index_append, IH],
    rw finset.sum_range_succ,
    congr' 1,
    { apply finset.sum_congr rfl,
      intros x hx,
      congr' 2,
      rw finset.mem_range at hx,
      rw list.nth_append hx, },
    { simp, } },
end

-- This is lemma 1.1
lemma aux2 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) 
  (dn₀ : n₀ = nat.find hf) (dα : α = real.log (f n₀) / real.log n₀) : 
    ∀ n : ℕ, f n ≤ n ^ α :=
begin
  have : f n₀ = n₀ ^ α,
  { rw [dα, real.log_div_log],
    apply eq.symm,
    apply real.rpow_logb,
    { norm_cast,
      exact lt_trans zero_lt_one (aux1 hf dn₀) },
    { apply ne_of_gt,
      norm_cast,
      exact aux1 hf dn₀ },
    { have hn₀ := nat.find_spec hf,
      rw ←dn₀ at hn₀,
      exact lt_trans zero_lt_one hn₀ } },
  have hα : 0 ≤ α,
  { rw dα,
    apply le_of_lt,
    apply div_pos,
    { apply real.log_pos,
      rw dn₀,
      exact nat.find_spec hf },
    { apply real.log_pos,
      norm_cast,
      exact aux1 hf dn₀ } },
  let C : ℝ := ((n₀ : ℝ) ^ α) / ((n₀ : ℝ) ^ α - 1),
  have hC : 0 ≤ C,
  {sorry}, -- easy to do
  suffices : ∀ n : ℕ, f n ≤ C * ((n : ℝ) ^ α),
  { intro n,
    have limit' : filter.tendsto (λ N : ℕ, C ^ (1 / (N : ℝ))) filter.at_top (nhds 1),
    {sorry}, --someone good at analysis
    have limit'' : filter.tendsto 
      (λ N : ℕ, (C ^ (1 / (N : ℝ))) * (n ^ α)) filter.at_top (nhds (n ^ α)),
    {sorry}, --following from limit'
    have stupid : (0 : ℝ) ≤ n := by norm_cast; exact zero_le n, -- very easy
    have aux : ∀ N : ℕ, (f (n)) ^ (N : ℝ) ≤ C * ((n ^ α) ^ (N : ℝ)),
    { intro N,
      rw ←real.rpow_mul stupid,
      nth_rewrite 1 mul_comm,
      rw real.rpow_mul stupid,
      norm_cast,
      rw ←mul_eq_pow,
      specialize this (n ^ N),
      norm_cast,
      exact this, },
    have aux1 : ∀ N : ℕ, f (n) ≤ (C ^ (1 / (N : ℝ))) * (n ^ α),
    {sorry},  --take nth root on both side
    exact ge_of_tendsto' limit'' aux1 },
  intro n,
  by_cases n = 0,
  { subst h,
    simp [hα],
    nlinarith [hC, real.zero_rpow_nonneg α] },
  have length_lt_one : 0 ≤ ((n₀.digits n).length : ℝ) - 1, -- Not sure whether this is useful or not
  { norm_num,
    sorry}, -- should be easy `digits_ne_nil_iff_ne_zero` might be useful
  conv_lhs { rw ←nat.of_digits_digits n₀ n },
  rw nat.of_digits_eq_sum_map_with_index,
  rw list.map_with_index_sum_to_finset_sum',
  simp only [nat.cast_sum, nat.cast_mul, nat.cast_pow],
  apply le_trans (Sum_le' (n₀.digits n).length _),
  have aux' : 2 ≤ n₀ := by linarith [aux1 hf dn₀],
  suffices goal_1 : ∑ i : finset.Iio (n₀.digits n).length,
    f (((((n₀.digits n).nth_le i (finset.mem_Iio.1 i.2))) : ℚ)
      * (n₀ : ℚ) ^ (i : ℕ)) = ∑ i : finset.Iio (n₀.digits n).length,
        f (((n₀.digits n).nth_le i (finset.mem_Iio.1 i.2))) 
          * (f n₀) ^ (i : ℕ),
  { rw goal_1,
    clear goal_1,
    have coef_ineq : ∀ i : finset.Iio (n₀.digits n).length,
      f (((n₀.digits n).nth_le i (finset.mem_Iio.1 i.2))) ≤ 1,
    { intro i,
      have : ((n₀.digits n).nth_le i (finset.mem_Iio.1 i.2)) < n₀,
      { have aux'' : ((n₀.digits n).nth_le i (finset.mem_Iio.1 i.2)) ∈ n₀.digits n,
        { exact (nat.digits n₀ n).nth_le_mem ↑i (finset.mem_Iio.mp i.property) },
        exact nat.digits_lt_base aux' aux'', },
      apply le_of_not_gt,
      subst dn₀,
      rw gt_iff_lt,
      exact nat.find_min hf this },
    rw this,
    have goal1 : ∑ (i : (finset.Iio (n₀.digits n).length)),
      f ((n₀.digits n).nth_le ↑i (finset.mem_Iio.1 i.2)) * (n₀ ^ α) ^ (i : ℕ) ≤
        ∑ (i : (finset.Iio (n₀.digits n).length)), (n₀ ^ α) ^ (i : ℕ),
    {sorry},
    apply le_trans goal1,
    clear goal1,
    have goal2 : (∑ i : (finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ α) ^ (i : ℕ)) =
    (((n₀ : ℝ) ^ (α * ((n₀.digits n).length - 1))) * 
      ∑ i : (finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ -α) ^ (i : ℕ)),
    {sorry},
    rw goal2,
    clear goal2,
    have goal3_aux : ∑ (i : (finset.Iio (n₀.digits n).length)),
      ((n₀ : ℝ) ^ -α) ^ (i : ℕ) ≤ ∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i,
    {sorry},
    have goal3_aux' : 0 ≤ (n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))),
    {sorry}, -- easy
    have goal3 : ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1)))) 
      * (∑ (i : (finset.Iio (n₀.digits n).length)), ((n₀ : ℝ) ^ -α) ^ (i : ℕ)) 
        ≤ ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1)))) * 
          (∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i),
    {sorry}, -- easy here
    apply le_trans goal3,
    clear goal3_aux goal3_aux' goal3,
    have goal4 : ∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i = C,
    {sorry}, -- `tsum_geometric_of_abs_lt_1` is useful here.
    rw goal4,
    clear goal4,
    rw mul_comm,
    suffices : (n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))) ≤ (n : ℝ) ^ α,
    { nlinarith },
    have goal : (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) ≤ (n : ℝ),
    { have h' := nat.base_pow_length_digits_le n₀ n aux' h,
      have h'' : (n₀ : ℝ) ^ ((n₀.digits n).length : ℝ) ≤ (n₀ : ℝ) * (n : ℝ),
      { norm_cast,
        exact h' },
      have aux'' : 0 < (n₀ : ℝ) := by norm_cast;linarith,
      have stupid : (n₀ : ℝ) ≠ 0 := by norm_cast;linarith,
      have h''' : 0 ≤ (n₀ : ℝ) ^ (-(1 : ℝ)),
      { rw real.rpow_neg_one,
        have stupid2 : 0 ≤ (n₀ : ℝ)⁻¹ * n₀ := by simp [inv_mul_cancel stupid],
        exact nonneg_of_mul_nonneg_left stupid2 aux'' },
      have h'''' := mul_le_mul_of_nonneg_left h'' h''',
      rw ←real.rpow_add aux'' _ _ at h'''',
      rw add_comm at h'''',
      rw ←mul_assoc at h'''',
      apply le_trans h'''',
      rw real.rpow_neg_one,
      rw inv_mul_cancel stupid,
      linarith },
    have stupid : (0 : ℝ) ≤ n₀ := sorry, -- easy
    rw mul_comm,
    rw real.rpow_mul stupid,
    have stupid2 : 0 ≤ (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) := sorry, --easy
    exact real.rpow_le_rpow stupid2 goal hα },
  { congr',
    ext,
    rw [f_mul_eq, mul_eq_pow] }
end

-- This is lemma 1.2 (this looks hard btw)
lemma aux3 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) 
  (dn₀ : n₀ = nat.find hf) (dα : α = real.log (f n₀) / real.log n₀) : 
    ∀ n : ℕ, (n ^ α : ℝ) ≤ f n :=
begin
  have hα : 0 ≤ α,
  { rw dα,
    apply le_of_lt,
    apply div_pos,
    { apply real.log_pos,
      rw dn₀,
      exact nat.find_spec hf },
    { apply real.log_pos,
      norm_cast,
      exact aux1 hf dn₀ } },
  have : f n₀ = n₀ ^ α := sorry, -- same proof as above
  let C : ℝ := (1 - (1 - 1 / n₀) ^ α),
  have hC : 0 ≤ C,
  {sorry}, -- Maybe useful later and easy to do
  suffices : ∀ n : ℕ, n ≠ 0 → C * ((n : ℝ) ^ α) ≤ f n, -- It seems to me that we need n ≠ 0 here.
  {sorry}, -- This should be almost the same as above
  intros n hn,
  have length_lt_one : 1 ≤ (n₀.digits n).length, -- Not sure whether this is useful or not
  {sorry}, -- should be easy `digits_ne_nil_iff_ne_zero` might be useful
  have h₁ : f ((n₀ : ℚ) ^ ((n₀.digits n).length)) 
    - f (((n₀ : ℚ) ^ ((n₀.digits n).length)) - n) ≤ f n,
  {sorry},
  apply le_trans' h₁,
  rw [mul_eq_pow, this],
  have h := aux2 hf dn₀ dα,
  specialize h ((n₀ ^ ((n₀.digits n).length)) - n),
  have h₂ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ ^ (n₀.digits n).length - n) : ℚ) ^ α ≤
  ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - f ((n₀ : ℚ) ^ (n₀.digits n).length - (n : ℚ)),
  {sorry},
  apply le_trans' h₂,
  clear h₂,
  simp only [rat.cast_sub, rat.cast_pow, rat.cast_coe_nat],
  have h₃ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ : ℝ) ^ (n₀.digits n).length - (n₀ : ℝ) ^ ((n₀.digits n).length - 1)) ^ α ≤
    ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ : ℝ) ^ (n₀.digits n).length - (n : ℝ)) ^ α,
  {sorry},
  apply le_trans' h₃,
  clear h₃,
  have h₄ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - 
    ((n₀ : ℝ) ^ (n₀.digits n).length - (n₀ : ℝ) ^ ((n₀.digits n).length - 1)) ^ α 
      = (((n₀ : ℝ) ^ α) ^ (n₀.digits n).length) * (1 - (1 - 1 / n₀) ^ α),
  { rw mul_sub,
    rw mul_one,
    rw sub_right_inj,
    repeat {rw ←real.rpow_nat_cast},
    rw ←real.rpow_mul,  -- This looks stupid here, as I am looking for (a ^ b) ^ c = (a ^ c) ^ b
    { nth_rewrite 1 mul_comm,
      rw real.rpow_mul,
      { rw ←real.mul_rpow,
        { rw mul_sub,
          rw mul_one,
          rw nat.cast_sub length_lt_one,
          rw real.rpow_sub,
          { ring_nf,
            simp only [algebra_map.coe_one, real.rpow_one] },
          norm_cast,
          linarith [aux1 hf dn₀] },
        { norm_cast,
          linarith [nat.one_le_pow ((n₀.digits n).length) 
            n₀ (by linarith [aux1 hf dn₀])] },
        { simp only [sub_nonneg],
          rw one_div_le,
          { simp only [div_self, ne.def, one_ne_zero, not_false_iff, nat.one_le_cast],
            linarith [aux1 hf dn₀] },
          { norm_cast,
            linarith [aux1 hf dn₀] },
          { linarith } } },
      norm_cast,
      exact nat.zero_le n₀ },
    norm_cast,
    exact nat.zero_le n₀ },
  rw h₄,
  clear h₄,
  change (1 - (1 - 1 / (n₀ : ℝ)) ^ α) with C,
  nth_rewrite 1 mul_comm,
  apply mul_le_mul_of_nonneg_left _ hC,
  suffices goal : (n : ℝ )^ α ≤ ((n₀ : ℝ) ^ (n₀.digits n).length) ^ α,
  { rw ←real.rpow_nat_cast at goal ⊢,
    rw ←real.rpow_mul, -- This looks stupid here, as I am looking for (a ^ b) ^ c = (a ^ c) ^ b
    { rw mul_comm,
      rw real.rpow_mul,
      { exact goal },
      norm_cast,
      exact nat.zero_le n₀ },
    norm_cast,
    exact nat.zero_le n₀ },
  have aux' : 2 ≤ n₀ := by linarith [aux1 hf dn₀],
  apply real.rpow_le_rpow,
  { norm_cast,
    exact nat.zero_le n },
  { norm_cast,
    linarith [@nat.lt_base_pow_length_digits _ n aux'] },
  { exact hα }
end

lemma archimedean_case (hf : ¬ is_nonarchimedean f) : mul_ring_norm.equiv f mul_ring_norm.real :=
begin
  rw ←non_archimedean_iff_nat_norm_bound at hf,
  simp only [not_forall, not_le] at hf,
  let n₀ : ℕ := nat.find hf,
  have dn₀ : n₀ = nat.find hf := rfl,
  let α : ℝ := real.log (f n₀) / real.log n₀,
  have hα : α =  real.log (f n₀) / real.log n₀ := rfl,
  have h₃ : ∀ (n : ℕ), f (n : ℚ) = (n : ℝ) ^ α,
  { intro n,
    linarith [aux3 hf dn₀ hα n, aux2 hf dn₀ hα n] },
  have h₄ : ∀ (n : ℕ), f (n : ℚ) = |n| ^ α,
  { intro n,
    rw nat.abs_cast n,
    exact h₃ n },
  apply mul_ring_norm.equiv_symm _ _,
  refine ⟨α, _, _⟩,
  { rw hα,
    apply div_pos,
    { apply real.log_pos,
      exact nat.find_spec hf },
    { apply real.log_pos,
      norm_cast,
      exact aux1 hf dn₀ } },
  { ext,
    rw mul_ring_norm_eq_abs,
    rw ←rat.num_div_denom x,
    norm_cast,
    rw ←rat.coe_int_div_eq_mk,
    rw abs_div,
    push_cast,
    rw ring_norm.div_eq,
    { rw real.div_rpow,
      { congr,
        { cases x.num with b b,
          { simp only [int.of_nat_eq_coe, int.cast_coe_nat],
            exact (h₄ b).symm },
          { simp only [int.cast_neg_succ_of_nat, nat.cast_add, algebra_map.coe_one,
              neg_add_rev],
            rw ←abs_neg,
            rw ←mul_ring_norm.neg,
            simp only [neg_add_rev, neg_neg],
            norm_cast,
            exact (h₃ (b + 1)).symm } },
        { exact (h₄ x.denom).symm } },
      { exact norm_nonneg ((x.num) : ℝ) },
      { exact norm_nonneg ((x.denom) : ℝ) } },
    { norm_cast,
      exact rat.denom_ne_zero x } },
end

end archimedean

/-- Ostrowski's Theorem -/
theorem rat_ring_norm_p_adic_or_real (f : mul_ring_norm ℚ) (hf_nontriv : f ≠ 1) :
  (mul_ring_norm.equiv f mul_ring_norm.real) ∨
  ∃ (p : ℕ) [hp : fact (nat.prime p)], mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) :=
begin
    by_cases bdd : ∀ z : ℕ, f z ≤ 1,
    { right, /- p-adic case -/
      rw [non_archimedean_iff_nat_norm_bound] at bdd,
      exact f_equiv_padic bdd hf_nontriv },
    { left,
      rw non_archimedean_iff_nat_norm_bound at bdd,
      exact archimedean_case bdd, /- Euclidean case -/ }
end