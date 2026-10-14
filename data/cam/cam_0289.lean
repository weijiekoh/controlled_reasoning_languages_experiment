import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-289»

structure RobustQuadraticProgram (n Ξ : Type) [Fintype n] where
  U : Set Ξ
  P : Ξ → Matrix n n ℝ
  q : Ξ → (n → ℝ)
  r : Ξ → ℝ
  constraints : Set (n → ℝ)

def RobustQuadraticProgram.objective
    {n Ξ : Type} [Fintype n]
    (p : RobustQuadraticProgram n Ξ) (x : n → ℝ) : ℝ :=
  sSup ((fun ξ => (1 / 2 : ℝ) * dotProduct x (p.P ξ *ᵥ x) + dotProduct (p.q ξ) x + p.r ξ) '' p.U)

def RobustQuadraticProgram.uncertaintySet
    {n Ξ : Type} [Fintype n]
    (p : RobustQuadraticProgram n Ξ) : Set Ξ :=
  p.U

structure SecondOrderConeProgram (n : Type) [Fintype n] where
  objective : AffineMap ℝ (n → ℝ) ℝ
  nonconicConstraints : Set ((n → ℝ) → Prop)
  nonconicConstraints_affine : ∀ g ∈ nonconicConstraints, ∃ a : AffineMap ℝ (n → ℝ) ℝ, g = fun x => a x ≤ 0
  coneConstraintCount : Type
  A : coneConstraintCount → (n → ℝ) → (n → ℝ)
  b : coneConstraintCount → (n → ℝ)
  c : coneConstraintCount → (n → ℝ)
  d : coneConstraintCount → ℝ

def SecondOrderConeProgram.isFeasible
    {n : Type} [Fintype n]
    (p : SecondOrderConeProgram n) (x : n → ℝ) : Prop :=
  (∀ g ∈ p.nonconicConstraints, g x) ∧
    ∀ i : p.coneConstraintCount, ‖p.A i x + p.b i‖ ≤ dotProduct (p.c i) x + p.d i

def SecondOrderConeProgram.objectiveValue
    {n : Type} [Fintype n]
    (p : SecondOrderConeProgram n) (x : n → ℝ) : ℝ :=
  p.objective x

structure EllipsoidalRobustQuadraticProgram
    (n m K : Type)
    [Fintype n]
    [Fintype m]
    [Fintype K]
    [DecidableEq K] extends RobustQuadraticProgram n (K → ℝ) where
  P0_matrix : Matrix n n ℝ
  Pi_matrix : K → Matrix n n ℝ
  q_fixed : n → ℝ
  r_fixed : ℝ
  A : Matrix m n ℝ
  b : m → ℝ
  P0_psd : P0_matrix.IsSymm ∧ ∀ x : n → ℝ, 0 ≤ dotProduct x (P0_matrix *ᵥ x)
  Pi_psd : ∀ i : K, (Pi_matrix i).IsSymm ∧ ∀ x : n → ℝ, 0 ≤ dotProduct x ((Pi_matrix i) *ᵥ x)
  uncertainty_eq :
    U = {u : K → ℝ | ‖u‖ ≤ (1 : ℝ)}
  P_eq :
    ∀ u : K → ℝ,
      P u = P0_matrix + ∑ i : K, u i • Pi_matrix i
  q_eq : q = fun _ => q_fixed
  r_eq : r = fun _ => r_fixed
  constraints_eq :
    constraints = {x : n → ℝ | ∀ i : m, dotProduct (fun j => A i j) x ≤ b i}
  feasible_nonempty : Set.Nonempty constraints

def EllipsoidalRobustQuadraticProgram.isFeasible
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    [DecidableEq K]
    (p : EllipsoidalRobustQuadraticProgram n m K) (x : n → ℝ) : Prop :=
  x ∈ p.constraints

def EllipsoidalRobustQuadraticProgram.uncertaintyMatrix
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    [DecidableEq K]
    (p : EllipsoidalRobustQuadraticProgram n m K) : Set (Matrix n n ℝ) :=
  Set.range p.P

structure EllipsoidalRobustQuadraticSOCP
    (n m K : Type)
    [Fintype n]
    [Fintype m]
    [Fintype K] where
  P0 : Matrix n n ℝ
  P : K → Matrix n n ℝ
  q : n → ℝ
  r : ℝ
  A_mat : Matrix m n ℝ
  b_vec : m → ℝ

def EllipsoidalRobustQuadraticSOCP.objective
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    (p : EllipsoidalRobustQuadraticSOCP n m K) (x : n → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (p.P0 *ᵥ x) + dotProduct p.q x + p.r + (1 / 2 : ℝ) * t

def EllipsoidalRobustQuadraticSOCP.feasible
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    (p : EllipsoidalRobustQuadraticSOCP n m K) (x : n → ℝ) (t : ℝ) : Prop :=
  (∀ i : m, dotProduct (fun j => p.A_mat i j) x ≤ p.b_vec i) ∧
    ‖fun k => dotProduct x (p.P k *ᵥ x)‖ ≤ t

def EllipsoidalRobustQuadraticSOCP.x
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    (_p : EllipsoidalRobustQuadraticSOCP n m K) (z : (n ⊕ Unit) → ℝ) : n → ℝ :=
  fun i => z (Sum.inl i)

def EllipsoidalRobustQuadraticSOCP.t
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    (_p : EllipsoidalRobustQuadraticSOCP n m K) (z : (n ⊕ Unit) → ℝ) : ℝ :=
  z (Sum.inr ())

def EllipsoidalRobustQuadraticSOCP.socVector
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    (p : EllipsoidalRobustQuadraticSOCP n m K) (z : (n ⊕ Unit) → ℝ) : K → ℝ :=
  fun k => dotProduct (p.x z) (p.P k *ᵥ p.x z)

theorem ellipsoidalRobustQuadraticProgram_equivalent_to_socp
    {n m K : Type}
    [Fintype n]
    [Fintype m]
    [Fintype K]
    [DecidableEq K]
    (p : EllipsoidalRobustQuadraticProgram n m K) :
    let socp : EllipsoidalRobustQuadraticSOCP n m K :=
      { P0 := p.P0_matrix
        P := p.Pi_matrix
        q := p.q_fixed
        r := p.r_fixed
        A_mat := p.A
        b_vec := p.b }
    (sInf
        {α : ℝ |
          ∃ x : n → ℝ,
            p.isFeasible x ∧
              RobustQuadraticProgram.objective p.toRobustQuadraticProgram x = α}) =
      (sInf
        {α : ℝ |
          ∃ x : n → ℝ, ∃ t : ℝ,
            socp.feasible x t ∧ socp.objective x t = α}) ∧
    (∀ x : n → ℝ,
      p.isFeasible x ∧
          RobustQuadraticProgram.objective p.toRobustQuadraticProgram x =
            sInf {α : ℝ |
              ∃ y : n → ℝ,
                p.isFeasible y ∧
                  RobustQuadraticProgram.objective p.toRobustQuadraticProgram y = α} ↔
        ∃ t : ℝ,
          socp.feasible x t ∧
            socp.objective x t =
              sInf {α : ℝ |
                ∃ y : n → ℝ, ∃ s : ℝ,
                  socp.feasible y s ∧ socp.objective y s = α}) := by
  sorry

end «CAM-Bench-289»
