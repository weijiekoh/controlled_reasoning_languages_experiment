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
  have key : ∀ x y : Fin n → ℝ, ∀ t : ℝ, 0 < t → f y + t * (f y - f x) ≤ M := by
    intro x y t ht
    have hpos : (0:ℝ) < 1 + t := by linarith
    have hy : y = (1/(1+t)) • (y + t • (y - x)) + (t/(1+t)) • x := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    have ha : (0:ℝ) ≤ 1/(1+t) := by positivity
    have hb : (0:ℝ) ≤ t/(1+t) := by positivity
    have hab : 1/(1+t) + t/(1+t) = 1 := by field_simp
    have h := hconv.2 (Set.mem_univ (y + t • (y - x))) (Set.mem_univ x) ha hb hab
    rw [← hy] at h
    simp only [smul_eq_mul] at h
    have hz := hM (y + t • (y - x))
    have e1 : (1+t)*(1/(1+t)) = 1 := by field_simp
    have e2 : (1+t)*(t/(1+t)) = t := by field_simp
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have h3 : (1+t) * (1/(1+t) * f (y + t • (y - x)) + t/(1+t) * f x)
        = f (y + t • (y - x)) + t * f x := by
      linear_combination (f (y + t • (y - x))) * e1 + (f x) * e2
    nlinarith
  have mono : ∀ x y : Fin n → ℝ, f y ≤ f x := by
    intro x y
    by_contra hc
    rw [not_le] at hc
    have hd : 0 < f y - f x := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (|M - f y| / (f y - f x))
    have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hlt : |M - f y| < (N:ℝ) * (f y - f x) := (div_lt_iff₀ hd).mp hN
    have := key x y N hNpos
    have := le_abs_self (M - f y)
    nlinarith
  refine ⟨f 0, fun x => le_antisymm ?_ ?_⟩
  · exact mono 0 x
  · exact mono x 0

end «CAM-Bench-578»
