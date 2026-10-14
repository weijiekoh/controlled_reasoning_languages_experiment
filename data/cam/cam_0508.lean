import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-508»

def euclideanNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

theorem max_norm_affine_convexOn_univ
    (k m n : ℕ)
    (hk : 0 < k)
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ)
    (b : Fin k → (Fin m → ℝ)) :
    ConvexOn ℝ Set.univ
      (fun x : Fin n → ℝ => ⨆ i : Fin k, euclideanNorm (A i *ᵥ x - b i)) := by
  sorry

end «CAM-Bench-508»
