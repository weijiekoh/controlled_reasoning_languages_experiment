import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-578»

theorem convex_bounded_above_on_univ_is_constant
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : ∀ x : Fin n → ℝ, f x ≤ M) :
    ∃ c : ℝ, ∀ x : Fin n → ℝ, f x = c := by
  have key : ∀ x y : Fin n → ℝ, f y ≤ f x := by
    intro x y
    by_contra h
    push_neg at h
    set d := f y - f x with hd
    have dpos : 0 < d := by linarith
    obtain ⟨t, ht⟩ := exists_gt (max 1 ((M - f x) / d) + 1)
    have t1 : 1 < t := by have := le_max_left 1 ((M - f x) / d); linarith
    have t0 : 0 < t := by linarith
    have t2 : (M - f x) / d < t := by have := le_max_right 1 ((M - f x) / d); linarith
    have t3 : M - f x < t * d := by rwa [div_lt_iff₀ dpos] at t2
    have ha : 0 ≤ 1 - 1/t := by rw [sub_nonneg, div_le_one t0]; linarith
    have hb : 0 ≤ 1/t := by positivity
    have hc := hconv.2 (Set.mem_univ x) (Set.mem_univ (x + t • (y - x)))
      ha hb (by ring)
    have e : (1 - 1/t) • x + (1/t) • (x + t • (y - x)) = y := by
      ext i
      simp
      field_simp
      ring
    rw [e] at hc
    have := hM (x + t • (y - x))
    simp only [smul_eq_mul] at hc
    have h5 : (1/t) * f (x + t • (y - x)) ≤ (1/t) * M := mul_le_mul_of_nonneg_left this (by positivity)
    have h6 : t * f y ≤ (t-1) * f x + M := by
      have e2 : t * ((1 - 1/t) * f x + 1/t * M) = (t-1) * f x + M := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h5 t0.le, e2, mul_le_mul_of_nonneg_left hc t0.le]
    nlinarith
  exact ⟨f 0, fun x => le_antisymm (key _ _) (key _ _)⟩

end «CAM-Bench-578»
