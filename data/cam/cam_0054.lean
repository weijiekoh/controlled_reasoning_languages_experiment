import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-54»

open Matrix

theorem orthogonal_projector_onto_ker_eq_two_forms
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix m n ℝ) (Z : Matrix n k ℝ)
    (hA : Function.Surjective A.toLin')
    (hZ :
      Submodule.span ℝ (Set.range fun j => Z.mulVec (fun k' => if k' = j then 1 else 0)) =
        LinearMap.ker A.toLin')
    (hZlin : LinearIndependent ℝ (fun j => Z.mulVec (fun k' => if k' = j then 1 else 0)))
    (rplus : n → ℝ) :
    let PperpZ := Z * (Z.transpose * Z)⁻¹ * Z.transpose
    let PperpA := (1 : Matrix n n ℝ) - A.transpose * (A * A.transpose)⁻¹ * A
    let gplusZ := PperpZ.mulVec rplus
    let gplusA := PperpA.mulVec rplus
    Nonempty (Invertible (A * A.transpose)) ∧ Nonempty (Invertible (Z.transpose * Z)) ∧
      PperpZ = PperpA ∧ gplusZ = gplusA := by
  sorry

end «CAM-Bench-54»
