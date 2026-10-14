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
  have hpos : ∀ i : Fin n, y i ≠ 0 := fun i => (hy i).ne'
  have hd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i))
      (∑ i : Fin n, ((y i) • (y i)⁻¹ • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        + (Real.log (y i)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))) y := by
    refine HasFDerivAt.fun_sum (fun i _ => ?_)
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z i) (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y :=
      by simpa using (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => Real.log (z i)) ((y i)⁻¹ • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y :=
      h1.log (hpos i)
    have h3 := h1.mul h2
    exact h3
  have hgrad : ∀ v : EuclideanSpace ℝ (Fin n), ⟪gradient (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i)) y, v⟫
      = ∑ i : Fin n, (Real.log (y i) + 1) * v i := by
    intro v
    rw [gradient, InnerProductSpace.toDual_symm_apply, hd.fderiv]
    simp [hpos]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpos i
    field_simp
    ring
  unfold bregmanDivergence
  rw [dif_pos ⟨fun i => hx i, fun i => hy i⟩]
  rw [hgrad]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Real.log_div (hx i).ne' (hy i).ne']
  ring

end «CAM-Bench-360»
