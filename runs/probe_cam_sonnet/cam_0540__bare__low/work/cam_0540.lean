import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-540»

def supportFunction (C : Set (Fin n → ℝ)) : (Fin n → ℝ) → WithTop ℝ :=
  fun y => sSup (((fun x : Fin n → ℝ => ((∑ i, y i * x i) : ℝ)) '' C) : Set (WithTop ℝ))

def minkowskiSum (A B : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

theorem supportFunction_minkowskiSum
    (A B : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    supportFunction (minkowskiSum A B) y = supportFunction A y + supportFunction B y := by
  sorry

end «CAM-Bench-540»
