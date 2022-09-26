/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed.ring.seminorm
import analysis.special_functions.pow

/-!
# Seminorm related definitions
## Tags
ring_norm, equivalent
-/

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def is_nonarchimedean {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A function `f : α → β` is `multiplicative` if it satisfies the equality
  `f (a * b) = (f a) * (f b)` for all `a, b ∈ α`. -/
def mul_eq {α : Type*} [has_mul α] {β : Type*} [has_mul β] [has_le β] (f : α → β) : Prop :=
∀ r s, f (r * s) = (f r) * (f s)

namespace ring_norm

/-- Two ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`. -/
def equiv {R : Type*} [ring R] (f : ring_norm R) (g : ring_norm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R, (f x) ^ c) = g

-- TODO: check that `equiv` is an equivalence relation.
lemma equiv_refl {R : Type*} [ring R] (f : ring_norm R) :
  equiv f f := by refine ⟨1, by linarith, by simp only [real.rpow_one]⟩

lemma equiv_symm {R : Type*} [ring R] (f g : ring_norm R) (hfg : equiv f g) :
  equiv g f :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  refine ⟨1 / c, by simp only [hfg1, one_div, inv_pos], _⟩,
  rw ← hfg2,
  ext,
  simp only [one_div],
  have h1 : c ≠ 0 := by linarith,
  rw ← real.rpow_mul (map_nonneg f x),
  simp only [h1, mul_inv_cancel, ne.def, not_false_iff, real.rpow_one],
end

lemma equiv_trans {R : Type*} [ring R] (f g k : ring_norm R) (hfg : equiv f g) (hgk : equiv g k) :
  equiv f k :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  rcases hgk with ⟨d, hgk1, hgk2⟩,
  refine ⟨c * d, by simp only [hfg1, hgk1, zero_lt_mul_right], _⟩,
  rw ← hgk2,
  rw ← hfg2,
  ext,
  exact real.rpow_mul (map_nonneg f x) c d,
end

end ring_norm

/- QUESTIONS :
  * What properties of `ring_norm` did you need to prove these lemmas?
  Nonneg
  * How far can `equiv` be generalized? -/
