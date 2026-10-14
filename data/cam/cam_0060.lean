import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-60»

open Matrix

theorem principal_submatrix_posDef_of_posDef
    {n t : ℕ} (ht : 2 ≤ t) (W : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin t) ℝ)
    (j : Fin t)
    (hW : W.IsSymm)
    (hpos : (Zᵀ * W * Z).PosDef) :
    let j' : Fin ((t - 1) + 1) :=
      Fin.cast (Nat.succ_pred_eq_of_pos (lt_of_lt_of_le (by decide : 0 < 2) ht)).symm j
    let Zbar : Matrix (Fin n) (Fin (t - 1)) ℝ :=
      Matrix.submatrix Z id (fun i : Fin (t - 1) =>
        Fin.cast (Nat.succ_pred_eq_of_pos (lt_of_lt_of_le (by decide : 0 < 2) ht))
          (Fin.succAbove j' i))
    (Zbar.transpose * W * Zbar).PosDef := by
  sorry

end «CAM-Bench-60»
