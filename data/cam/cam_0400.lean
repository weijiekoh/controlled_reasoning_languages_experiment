import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-400»

def kktSystem
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ) :
    Matrix (Sum n m) (Sum n m) ℝ × (Sum n m → ℝ) :=
  let K : Matrix (Sum n m) (Sum n m) ℝ :=
    Matrix.fromBlocks hess Aᵀ A 0
  let rhs : Sum n m → ℝ :=
    Sum.elim
      (fun i => -grad i)
      (fun j => -(A.mulVec x j - b j))
  (K, rhs)

def newtonStep
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ)
    (Δx : n → ℝ)
    (w : m → ℝ) : Prop :=
  let system := kktSystem hess A grad x b
  let K := system.1
  let rhs := system.2
  K.mulVec (Sum.elim Δx w) = rhs

structure SeparableEqualityConstrainedProblem where
  n : ℕ
  f : Fin n → ℝ → ℝ
  m : ℝ
  m_pos : 0 < m
  f_contDiff : ∀ i, ContDiff ℝ 2 (f i)
  hess_lower_bound : ∀ i z, m ≤ deriv (deriv (f i)) z

def SeparableEqualityConstrainedProblem.objective
    (P : SeparableEqualityConstrainedProblem) : (Fin P.n → ℝ) → ℝ :=
  fun x => ∑ i, P.f i (x i)

def SeparableEqualityConstrainedProblem.feasible
    (P : SeparableEqualityConstrainedProblem) : (Fin P.n → ℝ) → Prop :=
  fun x => (∑ i, x i) = 1

theorem newtonStep_computable_in_linear_time
    (P : SeparableEqualityConstrainedProblem)
    (x : Fin P.n → ℝ)
    (D : Matrix (Fin P.n) (Fin P.n) ℝ)
    (g : Fin P.n → ℝ)
    (hDdiag : ∀ i j, D i j = if i = j then deriv (deriv (P.f i)) (x i) else 0)
    (hDpos : ∀ i, 0 < D i i)
    (hg : ∀ i, g i = deriv (P.f i) (x i))
    (hx : P.feasible x)
    : let wScalar : ℝ := -((∑ i : Fin P.n, g i / D i i) / (∑ i : Fin P.n, (1 : ℝ) / D i i))
      let w : Fin 1 → ℝ := fun _ => wScalar
      let dx : Fin P.n → ℝ := fun i => -(g i + wScalar) / D i i
      newtonStep D (fun _ _ => 1) g x (fun _ => 1) dx w ∧
      ∃ C : ℕ, P.n ≤ C * P.n + C := by
  sorry

end «CAM-Bench-400»
