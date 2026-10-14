import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-21»

def LICQAt {ι : Type*} [Fintype ι] {n : ℕ}
    (g : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  LinearIndependent ℝ (fun i : ι => fderiv ℝ (g i) x)

def IsFeasiblePoint
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {ι : Type*}
    (g : ι → E → ℝ)
    (x : E)
    : Prop :=
  ∀ i : ι, 0 ≤ g i x

def IsOptimalSolution
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {ι : Type*}
    (f : E → ℝ)
    (g : ι → E → ℝ)
    (xstar : E)
    : Prop :=
  IsFeasiblePoint g xstar ∧ ∀ x : E, IsFeasiblePoint g x → f xstar ≤ f x

structure TwoConstraintNonlinearProgramData where
  objective : ℝ × ℝ → ℝ
  constraint1 : ℝ × ℝ → ℝ
  constraint2 : ℝ × ℝ → ℝ

def TwoConstraintNonlinearProgram : TwoConstraintNonlinearProgramData where
  objective := fun x => -2 * x.1 + x.2
  constraint1 := fun x => (1 - x.1) ^ 3 - x.2
  constraint2 := fun x => x.2 + (0.25 : ℝ) * x.1 ^ 2 - 1

def TwoConstraintNonlinearProgram.exercise1219a : TwoConstraintNonlinearProgramData :=
  TwoConstraintNonlinearProgram

def TwoConstraintNonlinearProgram.isFeasible
    (p : TwoConstraintNonlinearProgramData)
    (x : ℝ × ℝ) : Prop :=
  0 ≤ p.constraint1 x ∧ 0 ≤ p.constraint2 x

def TwoConstraintNonlinearProgram.feasibleSet
    (p : TwoConstraintNonlinearProgramData) : Set (ℝ × ℝ) :=
  {x | TwoConstraintNonlinearProgram.isFeasible p x}

def TwoConstraintNonlinearProgram.objectiveValue
    (p : TwoConstraintNonlinearProgramData)
    (x : ℝ × ℝ) : ℝ :=
  p.objective x

theorem exercise1219a_LICQ_holds_at_xstar :
    let p := TwoConstraintNonlinearProgram.exercise1219a
    let xstar : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
    LICQAt
      (fun i : Fin 2 =>
        match i.1 with
        | 0 => fun x : EuclideanSpace ℝ (Fin 2) => p.constraint1 (x 0, x 1)
        | _ => fun x : EuclideanSpace ℝ (Fin 2) => p.constraint2 (x 0, x 1))
      xstar := by
  sorry

end «CAM-Bench-21»
