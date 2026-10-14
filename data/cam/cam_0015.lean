import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-15»

open scoped BigOperators
open scoped RealInnerProductSpace

def SatisfiesKKT
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ)
    (g : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ := fun _ => 0) : Prop :=
  ∃ lam : ι → ℝ,
    gradient f x - ∑ i, lam i • gradient (g i) x = 0 ∧
      (∀ i, 0 ≤ g i x) ∧
      (∀ i, 0 ≤ lam i) ∧
      ∀ i, lam i * g i x = 0

def ComplementarySlackness
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (g : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  ∀ i, lam i * g i x = 0

structure QuarticConstrainedMinimization where
  t : ℝ
  objective : ℝ × ℝ → ℝ := fun x => (x.1 - (3 / 2 : ℝ)) ^ 2 + (x.2 - t) ^ 4
  constraint1 : ℝ × ℝ → Prop := fun x => 1 - x.1 - x.2 ≥ 0
  constraint2 : ℝ × ℝ → Prop := fun x => 1 - x.1 + x.2 ≥ 0
  constraint3 : ℝ × ℝ → Prop := fun x => 1 + x.1 - x.2 ≥ 0
  constraint4 : ℝ × ℝ → Prop := fun x => 1 + x.1 + x.2 ≥ 0

def QuarticConstrainedMinimization.feasibleSet (p : QuarticConstrainedMinimization) : Set (ℝ × ℝ) :=
  {x | p.constraint1 x ∧ p.constraint2 x ∧ p.constraint3 x ∧ p.constraint4 x}

def QuarticConstrainedMinimization.isFeasible
    (p : QuarticConstrainedMinimization) (x : ℝ × ℝ) : Prop :=
  x ∈ p.feasibleSet

def QuarticConstrainedMinimization.constraintFun
    (p : QuarticConstrainedMinimization) : Fin 4 → (ℝ × ℝ → ℝ)
  | 0 => fun x => 1 - x.1 - x.2
  | 1 => fun x => 1 - x.1 + x.2
  | 2 => fun x => 1 + x.1 - x.2
  | 3 => fun x => 1 + x.1 + x.2

def QuarticConstrainedMinimization.objectiveValue
    (p : QuarticConstrainedMinimization) (x : ℝ × ℝ) : ℝ :=
  p.objective x

theorem quarticConstrainedMinimization_kkt_at_one_zero_iff
    (t : ℝ) :
    (∃ lam : Fin 4 → ℝ,
      gradient
          (fun x : EuclideanSpace ℝ (Fin 2) =>
            (x 0 - (3 / 2 : ℝ)) ^ 2 + (x 1 - t) ^ 4)
          (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) -
        ∑ i,
          lam i •
            gradient
              (![
                (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 - x 1),
                (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 + x 1),
                (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 - x 1),
                (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 + x 1)
              ] i)
              (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) = 0 ∧
      (∀ i,
        0 ≤
          (![
            (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 - x 1),
            (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 + x 1),
            (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 - x 1),
            (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 + x 1)
          ] i)
            (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))) ∧
      (∀ i, 0 ≤ lam i) ∧
      (∀ i,
        lam i *
            (![
              (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 - x 1),
              (fun x : EuclideanSpace ℝ (Fin 2) => 1 - x 0 + x 1),
              (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 - x 1),
              (fun x : EuclideanSpace ℝ (Fin 2) => 1 + x 0 + x 1)
            ] i)
              (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) = 0)) ↔
      -((1 / 4 : ℝ)) ≤ t ^ 3 ∧ t ^ 3 ≤ (1 / 4 : ℝ) := by
  sorry

end «CAM-Bench-15»
