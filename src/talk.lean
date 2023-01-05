/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/
import basic
import mul_ring_norm_rat
import rationals

/-!
# Formaliszing Ostrowski's theorem in Lean

This is for presentation only.

-/

section absolute_value

-- Firstly let's look at "absolute value" in Lean.
-- Note that we can't sovle these sorrys as f is very "random".
def my_absolute_value (R : Type) [ring R] (f : R → ℝ) : mul_ring_norm R :=
{ to_fun := f,
  map_zero' := sorry,
  add_le' := sorry,
  neg' := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  eq_zero_of_map_eq_zero' := sorry }

-- Let's look at some examples we mentioned early.

--This is the usual absolute value on ℚ, these `sorrys` are doable.
def my_mul_ring_norm.real : mul_ring_norm ℚ :=
{ to_fun := λ x, |x|,
  map_zero' := by simp only [algebra_map.coe_zero, abs_zero],
  add_le' := sorry,
  neg' := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  eq_zero_of_map_eq_zero' := sorry }

-- This is the p-adic norm on ℚ, these `sorrys` are doable as well.
def my_mul_ring_norm.padic (p : ℕ) [hp : fact (nat.prime p)] : mul_ring_norm ℚ :=
{ to_fun    := λ x : ℚ, (padic_norm p x: ℝ),
  map_zero' := sorry,
  add_le'   := sorry,
  neg'      := sorry,
  eq_zero_of_map_eq_zero' := sorry,
  map_one' := sorry,
  map_mul' := sorry,
}

end absolute_value

section equiv

-- Here is how do we define the equivalance of two valuations.
def my_equiv {R : Type*} [ring R] (f : mul_ring_norm R) (g : mul_ring_norm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R, (f x) ^ c) = g

-- This is actually an equivalance relation.

lemma my_equiv_refl {R : Type*} [ring R] (f : mul_ring_norm R) :
  my_equiv f f := sorry

lemma my_equiv_symm {R : Type*} [ring R] (f g : mul_ring_norm R) (hfg : my_equiv f g) :
  my_equiv g f := sorry

lemma my_equiv_trans {R : Type*} [ring R] (f g k : mul_ring_norm R) 
  (hfg : my_equiv f g) (hgk : my_equiv g k) :
    my_equiv f k := sorry

end equiv

section nonarchimedean

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def my_is_nonarchimedean {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

lemma my_is_nonarchimedean_def {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) :
  my_is_nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) := iff.rfl

end nonarchimedean

variable {f : mul_ring_norm ℚ}

section nonarchimedean_proof

-- Firstly, we want to show it's bounded on all ℤ
-- but it suffices to consider it's bounded on all ℕ since |-x| = |x|
-- |n| = |1 + 1 + ...| ≤ |1| = 1 by the nonarchimedean property
lemma my_int_norm_le_one (harc : my_is_nonarchimedean f) (z : ℤ) : f z ≤ 1 := sorry

-- There is a prime number p such that f p < 1 
-- because, if not, unique prime factorization
-- would imply f x = 1 for all x in ℚ*.
lemma my_ex_prime_norm_lt_one (harc : my_is_nonarchimedean f) 
  (h_nontriv : f ≠ 1) : ∃ (p : ℕ) [hp : fact (nat.prime p)], f p < 1 := sorry

def my_α (harc : my_is_nonarchimedean f) : ideal ℤ :=
{ carrier := {a : ℤ | f a < 1},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry, }

lemma my_a_contains_prime_ideal (harc : my_is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc ≥ ideal.span {p} := sorry

lemma my_a_proper (harc : my_is_nonarchimedean f) : 𝔞 harc ≠ (⊤ : ideal ℤ) := sorry

-- Since pℤ is a maximal ideal.
lemma my_a_eq_prime_ideal (harc : my_is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)], 𝔞 harc = ideal.span {p} := sorry

-- if now a ∈ ℤ and a = bpᵐ with p ∤ b so thta b ∈ α,
-- then f b = 1 and hence
-- f a = (f p) ^ m = (padic_norm a) ^ s
-- where s = - log (f p) / log p 
lemma my_int_val_eq (harc : my_is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)] (s : ℝ) [hs : s > 0],
    ∀ (a : ℤ), f a = (@mul_ring_norm.padic p hp a) ^ s := sorry

-- f (p / q) = f p / f q
lemma my_rat_val_eq (harc : my_is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) [hp : fact (nat.prime p)] (s : ℝ) (hs : s > 0),
    ∀ (a : ℚ), f a = (@mul_ring_norm.padic p hp a) ^ s := sorry

lemma my_nonarchimedean_case (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) : 
 ∃ (p : ℕ) [hp : fact (nat.prime p)],
  mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) := sorry

end nonarchimedean_proof

section archimedean_proof

-- ∃ n : ℕ, f n > 1
lemma my_non_archimedean_iff_nat_norm_bound : 
  is_nonarchimedean f ↔ (∀ n : ℕ, f n ≤ 1) := sorry

-- Let n₀ = min{n : ℕ | f n > 1}
variables (hf : ∃ n : ℕ, 1 < f n) {n₀ : ℕ} (dn₀ : n₀ = nat.find hf)

-- f 1 = 1
lemma one_lt_n₀ : 1 < n₀ := sorry

variables {α : ℝ} (dα : α = real.log (f n₀) / real.log n₀)

-- 1 < n₀ and 1 < f n₀
lemma α_pos : 0 < α := sorry

lemma lemma1 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) 
  (dn₀ : n₀ = nat.find hf) (dα : α = real.log (f n₀) / real.log n₀) : 
    ∀ n : ℕ, f n ≤ n ^ α := sorry

lemma lemma2 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) 
  (dn₀ : n₀ = nat.find hf) (dα : α = real.log (f n₀) / real.log n₀) : 
    ∀ n : ℕ, (n ^ α : ℝ) ≤ f n := sorry

lemma my_archimedean_case (hf : ¬ is_nonarchimedean f) : 
  mul_ring_norm.equiv f mul_ring_norm.real := sorry

end archimedean_proof

/-- Ostrowski's Theorem -/
theorem ostrowski (f : mul_ring_norm ℚ) (hf_nontriv : f ≠ 1) :
  (mul_ring_norm.equiv f mul_ring_norm.real) ∨
  ∃ (p : ℕ) [hp : fact (nat.prime p)],
    mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) :=
begin
    by_cases bdd : ∀ z : ℕ, f z ≤ 1,
    { right, /- p-adic case -/
      rw ← my_non_archimedean_iff_nat_norm_bound at bdd,
      exact my_nonarchimedean_case bdd hf_nontriv },
    { left,
      rw ← my_non_archimedean_iff_nat_norm_bound at bdd,
      exact my_archimedean_case bdd, /- Euclidean case -/ }
end