import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-14»

def activeIndexSet {ι α : Type*} (g : ι → α → ℝ) (x : α) : Set ι :=
  {i | g i x = 0}

def LICQAt {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : ι → E → ℝ) (x : E) : Prop :=
  LinearIndependent ℝ (fun i : activeIndexSet g x => gradient (g i) x)

def MFCQAt {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : ι → E → ℝ) (x : E) : Prop :=
  ∃ d : E, ∀ i ∈ activeIndexSet g x, ⟪gradient (g i) x, d⟫ < 0

def IsFeasiblePoint {ι α : Type*} (g : ι → α → ℝ) (x : α) : Prop :=
  ∀ i, g i x ≤ 0

open scoped RealInnerProductSpace

theorem exercise_12_13_mfcq_holds_and_licq_fails_at_origin :
    let g : Fin 3 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun i x =>
        match i.1 with
        | 0 => (x 0 - 1) ^ 2 + (x 1 - 1) ^ 2 - 2
        | 1 => (x 0 - 1) ^ 2 + (x 1 + 1) ^ 2 - 2
        | _ => -x 0
    let xStar : EuclideanSpace ℝ (Fin 2) := 0
    IsFeasiblePoint g xStar ∧ MFCQAt g xStar ∧ ¬ LICQAt g xStar := by
  sorry

end «CAM-Bench-14»
