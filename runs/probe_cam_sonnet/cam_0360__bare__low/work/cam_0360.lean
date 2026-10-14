import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-360»

def bregmanDivergence {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (_grad_f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ := by
  classical
  by_cases hxy : x ∈ C ∧ y ∈ C
  · exact f x - f y - ⟪gradient f y, x - y⟫
  · exact 0

open scoped RealInnerProductSpace

theorem bregmanDivergence_eq_sum_xlog_ratio_sub_add {n : ℕ}
    (hn : 1 ≤ n)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ i : Fin n, 0 < x i)
    (hy : ∀ i : Fin n, 0 < y i) :
    bregmanDivergence
      {z : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, 0 < z i}
      (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i))
      (gradient (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i)))
      x y =
      ∑ i : Fin n, (x i * Real.log (x i / y i) - x i + y i) := by
  classical
  have hg : HasGradientAt (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i))
      (WithLp.toLp 2 (fun i => Real.log (y i) + 1)) y := by
    have h : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i))
        (∑ i : Fin n, (Real.log (y i) + 1) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by
      apply HasFDerivAt.fun_sum
      intro i _
      exact (Real.hasDerivAt_mul_log (hy i).ne').comp_hasFDerivAt y (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
    have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 fun i => Real.log (y i) + 1) = ∑ i : Fin n, (Real.log (y i) + 1) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      ext v
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    show HasFDerivAt _ (InnerProductSpace.toDual ℝ _ _) y
    rw [e]; exact h
  unfold bregmanDivergence
  rw [dif_pos ⟨hx, hy⟩, hg.gradient]
  simp only [PiLp.inner_apply, PiLp.sub_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_div (hx i).ne' (hy i).ne']
  simp
  ring

end «CAM-Bench-360»
