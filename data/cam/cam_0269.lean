import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-269»

open scoped BigOperators Matrix

theorem perspective_affine_convexOn
    {m n : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :
    ConvexOn ℝ
      {x : Fin n → ℝ | (∑ i, c i * x i) + d > 0}
      (fun x =>
        (((∑ i, c i * x i) + d)) *
          f (fun j => ((∑ i, A j i * x i) + b j) / (((∑ i, c i * x i) + d)))) := by
  sorry

end «CAM-Bench-269»
