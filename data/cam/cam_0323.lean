import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-323»

def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

def Lagrangian {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (h : Fin m → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) → ℝ :=
  fun x ν => f₀ x + ∑ i : Fin m, ν i * h i x

def DualVariables (m : ℕ) := Fin m → ℝ

def LagrangeDualFunction {n m : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ)
    (h : Fin m → (Fin n → ℝ) → ℝ) :
    DualVariables m → ℝ :=
  fun ν => sInf (Set.range (fun x : Fin n → ℝ => Lagrangian f₀ h x ν))

def LagrangeDualFunctionOfTwoBlocks {n p m : ℕ}
    (L : (Fin n → ℝ) → (Fin p → ℝ) → DualVariables m → ℝ) :
    DualVariables m → ℝ :=
  fun ν => sInf (Set.range (fun xy : (Fin n → ℝ) × (Fin p → ℝ) => L xy.1 xy.2 ν))

def LagrangeDualProblem {m : ℕ} (g : DualVariables m → ℝ) : ℝ :=
  sSup (Set.range g)

structure PrimalNonsmoothOptimizationProblem (n m : ℕ) where
  h : ℝ → ℝ
  c : Fin n → ℝ
  A : Fin m → (Fin n → ℝ) → (Fin 3 → ℝ)
  b : Fin m → Fin 3 → ℝ

def PrimalNonsmoothOptimizationProblem.objective {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin m, P.h (euclideanLength (y i))) - ∑ j : Fin n, P.c j * x j

def PrimalNonsmoothOptimizationProblem.feasible {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : Prop :=
  ∀ i : Fin m, (fun k : Fin 3 => P.A i x k + P.b i k - y i k) = 0

def PrimalNonsmoothOptimizationProblem.isSolution {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : Prop :=
  P.feasible x y ∧
    ∀ x' : Fin n → ℝ, ∀ y' : Fin m → Fin 3 → ℝ,
      P.feasible x' y' → P.objective x y ≤ P.objective x' y'

structure DualNonsmoothOptimizationProblem (n m : ℕ) where
  c : Fin n → ℝ
  A : Fin m → Matrix (Fin 3) (Fin n) ℝ
  b : Fin m → Fin 3 → ℝ

def DualNonsmoothOptimizationProblem.objective {n m : ℕ}
    (D : DualNonsmoothOptimizationProblem n m) (nu : Fin m → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin m,
    ((∑ k : Fin 3, D.b i k * nu i k) - euclideanLength (nu i) -
      (1 / 2 : ℝ) * euclideanLength (nu i) ^ 2)

def DualNonsmoothOptimizationProblem.feasible {n m : ℕ}
    (D : DualNonsmoothOptimizationProblem n m) (nu : Fin m → Fin 3 → ℝ) : Prop :=
  ∀ j : Fin n,
    ∑ i : Fin m, ((D.A i).transpose.mulVec (nu i)) j = D.c j

def DualNonsmoothOptimizationProblem.isSolution {n m : ℕ}
    (D : DualNonsmoothOptimizationProblem n m) (nu : Fin m → Fin 3 → ℝ) : Prop :=
  D.feasible nu ∧
    ∀ nu' : Fin m → Fin 3 → ℝ,
      D.feasible nu' → D.objective nu' ≤ D.objective nu

theorem lagrangeDualFunction_eq_piecewise_for_nonsmooth_problem
    {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (h_def : P.h = fun u : ℝ => if 1 ≤ u then (u - 1) ^ 2 / 2 else 0) :
    ∀ ν : Fin m → Fin 3 → ℝ,
      let D : DualNonsmoothOptimizationProblem n m :=
        { c := P.c
          A := fun i => fun k j => P.A i (Pi.single j (1 : ℝ)) k
          b := P.b }
      (sInf
        (Set.range
          (fun xy : (Fin n → ℝ) × (Fin m → Fin 3 → ℝ) =>
            show EReal from
              (((∑ i : Fin m,
                    (P.h (euclideanLength (xy.2 i)) + (∑ k : Fin 3, ν i k * P.b i k) -
                      (∑ k : Fin 3, ν i k * xy.2 i k))) +
                  ((∑ i : Fin m, ∑ k : Fin 3, ν i k * P.A i xy.1 k) -
                    ∑ j : Fin n, P.c j * xy.1 j)) : ℝ))) =
        if ∀ j : Fin n,
            ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j then
          ((∑ i : Fin m,
              ((∑ k : Fin 3, P.b i k * ν i k) - euclideanLength (ν i) -
                (1 / 2 : ℝ) * euclideanLength (ν i) ^ 2) : ℝ) : EReal)
        else ⊥) ∧
      (D.feasible ν ↔
        ∀ j : Fin n,
          ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j) ∧
      (D.objective ν =
        ∑ i : Fin m,
          ((∑ k : Fin 3, P.b i k * ν i k) - euclideanLength (ν i) -
            (1 / 2 : ℝ) * euclideanLength (ν i) ^ 2)) := by
  sorry

end «CAM-Bench-323»
