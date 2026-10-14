import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-218»

structure DosePlanningConvexProgram where
  m : ℕ
  n : ℕ
  T : Finset (Fin m)
  A : Fin m → Fin n → ℝ
  Bmax : ℝ
  Dtarget : ℝ
  Dother : ℝ

def DosePlanningConvexProgram.decisionSet
    (p : DosePlanningConvexProgram) : Set (Fin p.n → ℝ) :=
  Set.univ

def DosePlanningConvexProgram.feasible
    (p : DosePlanningConvexProgram) (b : Fin p.n → ℝ) : Prop :=
  (∀ j : Fin p.n, 0 ≤ b j ∧ b j ≤ p.Bmax) ∧
    ∀ i ∈ p.T, (∑ j : Fin p.n, p.A i j * b j) ≥ p.Dtarget

def DosePlanningConvexProgram.objectiveFun
    (p : DosePlanningConvexProgram) (b : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m,
    if i ∈ p.T then
      0
    else
      (max ((∑ j : Fin p.n, p.A i j * b j) - p.Dother) 0) ^ 2

def DosePlanningConvexProgram.dose (p : DosePlanningConvexProgram) (i : Fin p.m) (b : Fin p.n → ℝ) : ℝ :=
  ∑ j : Fin p.n, p.A i j * b j

def DosePlanningConvexProgram.isFeasible (p : DosePlanningConvexProgram) (b : Fin p.n → ℝ) : Prop :=
  (∀ j : Fin p.n, 0 ≤ b j ∧ b j ≤ p.Bmax) ∧
    ∀ i ∈ p.T, p.dose i b ≥ p.Dtarget

def DosePlanningConvexProgram.objective (p : DosePlanningConvexProgram) (b : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m,
    if i ∈ p.T then
      0
    else
      (max (p.dose i b - p.Dother) 0) ^ 2

theorem dosePlanningConvexProgram_isConvex (p : DosePlanningConvexProgram) :
    Convex ℝ {b : Fin p.n → ℝ | p.isFeasible b} ∧
      ConvexOn ℝ {b : Fin p.n → ℝ | p.isFeasible b} p.objective := by
  sorry

end «CAM-Bench-218»
