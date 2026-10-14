import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-58»

theorem rank_eq_of_block_kkt_invertible
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hK :
      Function.Injective
        (Matrix.toLin'
          (Matrix.fromBlocks G A.transpose A 0 :
            Matrix (Sum (Fin n) (Fin m)) (Sum (Fin n) (Fin m)) ℝ))) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = m := by
  sorry

end «CAM-Bench-58»
