/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import number_theory.padics.padic_norm
import basic
import order.filter.basic

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

lemma norm_pos_of_ne_zero {x : ℚ} (h : x ≠ 0) : f x > 0 :=
lt_of_le_of_ne (map_nonneg f x) (λ h', h (f.eq_zero_of_map_eq_zero' x h'.symm))

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

-- I couldn't find this lemma in mathlib. A similar version in mathlib is `one_le_prod_of_one_le`.
lemma real.one_le_prod_of_one_le {l : list ℝ} (hl : ∀ x : ℝ, x ∈ l → 1 ≤ x) : 1 ≤ l.prod :=
begin
  induction l with a l ih,
  { simp only [list.prod_nil], },
  { simp only [list.prod_cons],
    have goal := (ih $ λ a ha, hl a $ list.mem_cons_of_mem _ ha),
    have goal1 := (hl _ $ list.mem_cons_self _ _),
    nlinarith, },
end

-- Show that there is a prime with norm < 1
lemma ex_prime_norm_lt_one (heq : mul_eq f) (harc : is_nonarchimedean f) 
  (h : f ≠ 1) : ∃ (p : ℕ) [hp : fact (nat.prime p)], f p < 1 :=
begin
  by_contra',
  obtain ⟨n, hn1, hn2⟩ := nat_nontriv_of_rat_nontriv heq harc h,
  rw ← nat.prod_factors hn1 at hn2,
  have exp : ∀ q : ℕ, q ∈ nat.factors n → 1 ≤ f q,
  { intros q hq,
    letI : fact (nat.prime q) := {out := nat.prime_of_mem_factors hq},
    specialize this q,
    exact this, },
  simp only [nat.cast_list_prod] at hn2,
  have hf_mh: f.to_fun = (f.to_monoid_hom heq).to_fun := rfl,
  rw [← f.to_fun_eq_coe, hf_mh, (f.to_monoid_hom heq).to_fun_eq_coe, map_list_prod] at hn2,
  simp only [list.map_map] at hn2,
  have h : ∀ (x ∈ (list.map ((f.to_monoid_hom heq) ∘ (coe : ℕ → ℚ)) n.factors)), 1 ≤ x,
  { intros x hx,
    simp only [list.mem_map, function.comp_app] at hx,
    rcases hx with ⟨a, ha1, ha2⟩,
    letI : fact (nat.prime a) := {out := nat.prime_of_mem_factors ha1},
    specialize exp a ha1,
    rw ← ha2,
    convert exp, },
  have goal := real.one_le_prod_of_one_le h,
  linarith,
end

lemma prime_triv_nat_triv (heq : mul_eq f) (harc : is_nonarchimedean f) 
  (H : ∀ p : ℕ , p.prime → f p = 1) : ∀ n : ℕ, n ≠ 0 → f n = 1 :=
begin
  intros n n_pos,
  induction n using nat.strong_induction_on with n hn,
  by_cases nge2 : n < 2,
  { interval_cases n,
    { exfalso, apply n_pos, refl },
    { exact norm_one_eq_one heq } },
  { push_neg at hn,
    have : n ≠ 1,
    { intro H,
      rw H at nge2,
      apply nge2,
      norm_num },
    obtain ⟨p, p_prime, p_div⟩ := nat.exists_prime_and_dvd this,
    obtain ⟨k, hk⟩ := p_div,
    rw hk,
    rw nat.cast_mul,
    rw heq,
    rw H p p_prime,
    rw one_mul,
    have k_pos : k ≠ 0,
    { intro k_zero, apply n_pos, rw hk, rw k_zero, rw mul_zero },
    have kltn : k < n,
    { have := nat.prime.two_le p_prime,
      rw hk,
      have ineq1 : 2*k ≤ p*k,
      { exact mul_le_mul_right' this k },
      have ineq2 : k < 2 * k,
      { nth_rewrite 0 ←one_mul k,
        have : 0 < k,
        { exact zero_lt_iff.mpr k_pos },
        apply (mul_lt_mul_right this).mpr,
        norm_num, },
      exact lt_of_lt_of_le ineq2 ineq1 },
    exact hn k kltn k_pos }
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

lemma a_proper (harc : is_nonarchimedean f) (heq : mul_eq f) : 𝔞 harc heq ≠ (⊤ : ideal ℤ) :=
begin
  intro h,
  have : (1 : ℤ) ∉ (𝔞 harc heq),
  { 
    unfold 𝔞,
    simp only [submodule.mem_mk, set.mem_set_of_eq, int.cast_one, not_lt],
    exact (norm_one_eq_one heq).ge,
  },
  rw h at this,
  apply this,
  exact trivial,
end

-- Show that it contains pZ
lemma a_contains_prime_ideal (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc heq ≥ ideal.span {p} :=
begin
  obtain ⟨p, hp, hbound⟩ := ex_prime_norm_lt_one heq harc h_nontriv,
  use p,
  split, { exact hp },
  { apply ideal.span_le.mpr,
    intros ppr hp,
    unfold 𝔞,
    simp only [set.mem_singleton_iff] at hp,
    simp only [submodule.coe_set_mk, set.mem_set_of_eq],
    rw hp,
    exact hbound }
end

-- Show that it's in fact equal to pZ (since pZ is a maximal ideal)
lemma a_eq_prime_ideal (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc heq = ideal.span {p} :=
begin
  obtain ⟨p, hp, hinc⟩ := a_contains_prime_ideal harc heq h_nontriv,
  use p,
  split, { exact hp },
  cases hp,
  have h_irr : irreducible (p : ℤ) := (nat.prime_iff_prime_int.mp hp).irreducible,
  have hmax : ideal.is_maximal (ideal.span ({p} : set ℤ)) :=
    principal_ideal_ring.is_maximal_of_irreducible h_irr,
  symmetry,
  exact hmax.eq_of_le (a_proper harc heq) hinc,
end

lemma mult_finite {a : ℤ} {p : ℕ} (hprime : nat.prime p) (ha : a ≠ 0) :
  multiplicity.finite (p : ℤ) a :=
begin
  apply multiplicity.finite_int_iff.mpr,
  simp only [ha, hprime.ne_one, int.nat_abs_of_nat, ne.def, not_false_iff, and_self],
end

lemma mul_eq_pow (heq : mul_eq f) {a : ℚ} {n : ℕ} : f (a ^ n) = (f a) ^ n :=
begin
  induction n with d hd,
  simp only [pow_zero],
  exact norm_one_eq_one heq,
  rw [pow_succ, pow_succ, ←hd, heq],
end

-- the equality at the end of the next lemma
lemma arithmetic {p v : ℝ} (m : ℕ) (hp : p > 0) (hlogp : real.log p ≠ 0) (hv : v > 0) : v ^ m = (p ^ m)⁻¹ ^ (-real.log v / real.log p) :=
begin
  rw ←real.rpow_neg_one,
  have : p ^ m = p ^ (m : ℝ) := by norm_cast,
  rw [this, ←(real.rpow_mul (le_of_lt hp)), ←(real.rpow_mul (le_of_lt hp)), neg_div],
  simp only [mul_neg, mul_one, neg_mul, neg_neg],
  rw [mul_div, ←real.log_rpow hv, real.rpow_def_of_pos hp, mul_div_left_comm,
    div_self hlogp, mul_one, real.exp_log],
  { norm_cast },
  norm_cast,
  exact pow_pos hv m,
end

-- f a = (f p)^m = ring_norm a
lemma int_val_eq (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)] (s : ℝ), ∀ (a : ℤ), f a = (@ring_norm.padic p hp a)^s :=
begin
  obtain ⟨p, hprime, h_aeq⟩ := a_eq_prime_ideal harc heq h_nontriv,
  use p,
  use hprime,
  cases hprime,
  have pneq0 : (p : ℚ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (nat.prime.pos hprime)),
  have fpgt0 := norm_pos_of_ne_zero pneq0,
  have hlogp : real.log p ≠ 0 := real.log_ne_zero_of_pos_of_ne_one
    (nat.cast_pos.mpr (nat.prime.pos hprime))
    (nat.cast_ne_one.mpr (nat.prime.ne_one hprime)),
  let s := (-real.log (f p : ℝ) / real.log p),
  use s,
  intro a,
  by_cases ha : a = 0,
  { rw ha,
    have hs : s ≠ 0,
    { have fpneq1 : (f p) ≠ 1, -- prove this through p ∈ 𝔞 through h_aeq
      { have p_mem_a : (p : ℤ) ∈ ideal.span ({p} : set ℤ) := by rw ideal.mem_span_singleton,
        rw ←h_aeq at p_mem_a,
        unfold 𝔞 at p_mem_a,
        simp only [submodule.mem_mk, set.mem_set_of_eq, int.cast_coe_nat] at p_mem_a,
        exact ne_of_lt p_mem_a },
      have hlogfp : real.log (f p) ≠ 0 := real.log_ne_zero_of_pos_of_ne_one fpgt0 fpneq1,
      exact div_ne_zero (neg_ne_zero.mpr hlogfp) hlogp },
    simp only [hs, int.cast_zero, map_zero, real.zero_rpow, ne.def, not_false_iff] },
  have hfin := mult_finite hprime ha,
  obtain ⟨b, hapb, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hfin,
  let m := (multiplicity (p : ℤ) a).get hfin,
  have : f a = (f p) ^ m,
  { rw hapb,
    have hb : ↑b ∉ 𝔞 harc heq,
    { rw h_aeq,
      intro hmem,
      rw ideal.mem_span_singleton' at hmem,
      obtain ⟨k, hk⟩ := hmem,
      apply hndiv,
      rw dvd_iff_exists_eq_mul_left,
      use k,
      exact hk.symm },
    unfold 𝔞 at hb,
    simp only [int.cast_id, submodule.mem_mk, set.mem_set_of_eq, not_lt] at hb,
    have h' : f b = 1 := le_antisymm (int_norm_le_one b heq harc) hb,
    have h'' : f ((p : ℚ) ^ m * (b : ℚ)) = (f (p : ℚ)) ^ m,
    { rw [heq, h'],
      rw mul_one,
      exact mul_eq_pow heq },
    convert h'',
    norm_cast,
  },
  rw this,
  simp [ring_norm_eq_padic_norm, ha],
  unfold padic_val_int padic_val_nat,
  simp [ha, hprime.ne_one, int.nat_abs_pos_of_ne_zero ha, multiplicity.int.nat_abs p a],
  have hppos : (p : ℝ) > 0 := nat.cast_pos.mpr (hprime.pos),
  exact arithmetic m hppos hlogp fpgt0,
end

-- Extend this to ℚ using div_eq

-- Finish: hence f and padic are equivalent
lemma f_equiv_padic (harc : is_nonarchimedean f) (heq : mul_eq f) (h_nontriv : f ≠ 1) : 
 ∃ (p : ℕ) [hp : fact (nat.prime p)], ring_norm.equiv f (@ring_norm.padic p hp) :=
begin
sorry,
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

--First limit
lemma limit1 {N : ℝ} (hN : 1 ≤ N) : filter.tendsto (λ n : ℕ, N ^ (1 / n)) filter.at_top (nhds 1) :=
sorry

--Second limit
lemma limit2 {c : ℝ} (hc : 0 ≤ c) : filter.tendsto (λ n : ℕ, (1 + (n : ℝ)*c)^(1 / n)) filter.at_top (nhds 1) :=
sorry

-- A norm is non-archimedean iff it's bounded on the naturals
lemma non_archimidean_iff_nat_norm_bound (hmul : mul_eq f) : (∀ n : ℕ, f n ≤ 1) ↔ is_nonarchimedean f :=
begin
  split,
  { sorry },
  { intros hf n,
    exact nat_norm_leq_one n hmul hf }
end


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