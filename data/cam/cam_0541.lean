import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-541»

def supportFunction (C : Set (Fin n → ℝ)) : (Fin n → ℝ) → EReal :=
  fun y => sSup ((fun x : Fin n → ℝ => ((∑ i, y i * x i : ℝ) : EReal)) '' C)

theorem supportFunction_union (A B : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    supportFunction (A ∪ B) y = max (supportFunction A y) (supportFunction B y) := by
  sorry

end «CAM-Bench-541»
