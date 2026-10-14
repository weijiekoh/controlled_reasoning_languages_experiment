import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-354»

def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ u ∈ C, ∑ i, u i * x i ≤ 1}

def IsPolyhedron (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    C = {x | ∀ i, ∑ j, A i j * x j ≤ b i}

structure QuadraticProgram where
  n : ℕ
  meq : ℕ
  mineq : ℕ
  Q : Fin n → Fin n → ℝ
  c : Fin n → ℝ
  r : ℝ
  Aeq : Fin meq → Fin n → ℝ
  beq : Fin meq → ℝ
  Aineq : Fin mineq → Fin n → ℝ
  bineq : Fin mineq → ℝ
  Q_symm : Matrix.IsSymm Q

def QuadraticProgram.objective (P : QuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, x i * P.Q i j * x j) + (∑ i, P.c i * x i) + P.r

def QuadraticProgram.eqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aeq i j * x j = P.beq i

def QuadraticProgram.ineqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aineq i j * x j ≤ P.bineq i

def QuadraticProgram.FeasibleSet (P : QuadraticProgram) : Set (Fin P.n → ℝ) :=
  {x | QuadraticProgram.eqFeasible P x ∧ QuadraticProgram.ineqFeasible P x}

structure PolarDistanceMinimization where
  n : ℕ
  C₁ : Set (Fin n → ℝ)
  C₂ : Set (Fin n → ℝ)

def PolarDistanceMinimization.isFeasible
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : Prop :=
  x₁ ∈ polar P.C₁ ∧ x₂ ∈ polar P.C₂

def PolarDistanceMinimization.objective
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceMinimization.feasibleSet
    (P : PolarDistanceMinimization) : Set ((Fin P.n → ℝ) × (Fin P.n → ℝ)) :=
  {(x₁, x₂) | P.isFeasible x₁ x₂}

structure PolarDistanceQP where
  n : ℕ
  m₁ : ℕ
  m₂ : ℕ
  A₁ : Fin m₁ → Fin n → ℝ
  b₁ : Fin m₁ → ℝ
  A₂ : Fin m₂ → Fin n → ℝ
  b₂ : Fin m₂ → ℝ

def PolarDistanceQP.isFeasible
    (P : PolarDistanceQP)
    (x₁ x₂ : Fin P.n → ℝ)
    (lam₁ : Fin P.m₁ → ℝ)
    (lam₂ : Fin P.m₂ → ℝ) : Prop :=
  (∀ i, ∑ j, P.A₁ j i * lam₁ j = x₁ i) ∧
  (∑ j, P.b₁ j * lam₁ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₁ j) ∧
  (∀ i, ∑ j, P.A₂ j i * lam₂ j = x₂ i) ∧
  (∑ j, P.b₂ j * lam₂ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₂ j)

def PolarDistanceQP.objective
    (P : PolarDistanceQP) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceQP.feasibleSet
    (P : PolarDistanceQP) :
    Set ((Fin P.n → ℝ) × (Fin P.n → ℝ) × (Fin P.m₁ → ℝ) × (Fin P.m₂ → ℝ)) :=
  {y | P.isFeasible y.1 y.2.1 y.2.2.1 y.2.2.2}

theorem polar_distance_minimization_equivalent_to_quadratic_program_reformulation
    (n m₁ m₂ : ℕ)
    (A₁ : Fin m₁ → Fin n → ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Fin m₂ → Fin n → ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hC₁ :
      {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i} ≠ (∅ : Set (Fin n → ℝ)))
    (hC₂ :
      {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i} ≠ (∅ : Set (Fin n → ℝ))) :
    let P : PolarDistanceMinimization := {
      n := n
      C₁ := {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i}
      C₂ := {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i}
    }
    let QP : PolarDistanceQP := {
      n := n
      m₁ := m₁
      m₂ := m₂
      A₁ := A₁
      b₁ := b₁
      A₂ := A₂
      b₂ := b₂
    }
    ∀ x₁ x₂ : Fin n → ℝ,
      P.isFeasible x₁ x₂ ↔
        ∃ lam₁ : Fin m₁ → ℝ, ∃ lam₂ : Fin m₂ → ℝ,
          QP.isFeasible x₁ x₂ lam₁ lam₂ := by
  sorry

end «CAM-Bench-354»
