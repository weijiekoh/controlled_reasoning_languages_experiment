import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-687»

def decisionVariable {α : Type*} (feasibleSet : Set α) (x : α) : Prop :=
  x ∈ feasibleSet

def optimalVector {α : Type*} (feasibleSet : Set α) (objective : α → ℝ) (x : α) : Prop :=
  x ∈ feasibleSet ∧ ∀ y, y ∈ feasibleSet → objective x ≤ objective y

def linearSystem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (x : n → ℝ) (b : m → ℝ) : Prop :=
  A.mulVec x = b

structure GraphEmbeddingLeastSquaresProblem where
  N : ℕ
  M : ℕ
  hM_pos : 1 ≤ M
  hMN : M ≤ N
  edges : Finset (Fin N × Fin N)
  fixedData : ∀ i : Fin N, M ≤ i.1 → Fin 2 → ℝ

def GraphEmbeddingLeastSquaresProblem.isDecisionVertex (p : GraphEmbeddingLeastSquaresProblem)
    (i : Fin p.N) : Prop :=
  i.1 < p.M

def GraphEmbeddingLeastSquaresProblem.isGivenVertex (p : GraphEmbeddingLeastSquaresProblem)
    (i : Fin p.N) : Prop :=
  p.M ≤ i.1

def GraphEmbeddingLeastSquaresProblem.fullAssignment (p : GraphEmbeddingLeastSquaresProblem)
    (x : Fin p.M → Fin 2 → ℝ) : Fin p.N → Fin 2 → ℝ :=
  fun i =>
    if h : i.1 < p.M then
      x ⟨i.1, h⟩
    else
      p.fixedData i (le_of_not_gt h)

def GraphEmbeddingLeastSquaresProblem.objective
    (p : GraphEmbeddingLeastSquaresProblem) (x : Fin p.M → Fin 2 → ℝ) : ℝ :=
  let X := p.fullAssignment x
  ∑ e ∈ p.edges, ‖X e.1 - X e.2‖ ^ 2

def GraphEmbeddingLeastSquaresProblem.feasibleSet
    (p : GraphEmbeddingLeastSquaresProblem) : Set (Fin p.M → Fin 2 → ℝ) :=
  Set.univ

theorem graphEmbeddingLeastSquares_optimal_vectors_satisfy_symmetric_linear_systems
    (p : GraphEmbeddingLeastSquaresProblem) :
    ∃ C : Matrix (Fin p.M) (Fin p.M) ℝ,
      Matrix.IsSymm C ∧
      (∀ i j : Fin p.M,
        C i j =
          if i = j then
            (((p.edges.filter (fun e => e.1.1 = i.1 ∨ e.2.1 = i.1)).card : ℕ) : ℝ)
          else
            -((((p.edges.filter (fun e =>
                (e.1.1 = i.1 ∧ e.2.1 = j.1) ∨
                (e.1.1 = j.1 ∧ e.2.1 = i.1))).card : ℕ) : ℝ))) ∧
      ∀ x : Fin p.M → Fin 2 → ℝ,
        optimalVector p.feasibleSet p.objective x →
        let u : Fin p.M → ℝ := fun i => x i 0
        let v : Fin p.M → ℝ := fun i => x i 1
        let d₁ : Fin p.M → ℝ := fun i =>
          ∑ e ∈ p.edges,
            if h1 : e.1.1 = i.1 ∧ p.M ≤ e.2.1 then p.fixedData e.2 h1.2 0
            else if h2 : e.2.1 = i.1 ∧ p.M ≤ e.1.1 then p.fixedData e.1 h2.2 0
            else 0
        let d₂ : Fin p.M → ℝ := fun i =>
          ∑ e ∈ p.edges,
            if h1 : e.1.1 = i.1 ∧ p.M ≤ e.2.1 then p.fixedData e.2 h1.2 1
            else if h2 : e.2.1 = i.1 ∧ p.M ≤ e.1.1 then p.fixedData e.1 h2.2 1
            else 0
        linearSystem C u d₁ ∧ linearSystem C v d₂ := by
  sorry

end «CAM-Bench-687»
