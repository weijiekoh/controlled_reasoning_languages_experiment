import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-352»

def IsPolyhedron {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ b : Fin m → ℝ,
    C = {x | ∀ i : Fin m, (∑ j : Fin n, A i j * x j) ≤ b i}

def LagrangeDualProblem
    {n m p : ℕ}
    (f0 : (Fin n → ℝ) → ℝ)
    (f : Fin m → (Fin n → ℝ) → ℝ)
    (h : Fin p → (Fin n → ℝ) → ℝ) :
    Set ((Fin m → ℝ) × (Fin p → ℝ)) :=
  let g : ((Fin m → ℝ) × (Fin p → ℝ)) → ℝ :=
    fun yz =>
      sInf
        (Set.range fun x : Fin n → ℝ =>
          f0 x + (∑ i : Fin m, yz.1 i * f i x) + ∑ j : Fin p, yz.2 j * h j x)
  { yz : (Fin m → ℝ) × (Fin p → ℝ) |
      (∀ i : Fin m, 0 ≤ yz.1 i) ∧
        ∀ yz' : (Fin m → ℝ) × (Fin p → ℝ), (∀ i : Fin m, 0 ≤ yz'.1 i) → g yz' ≤ g yz }

def Lagrangian
    {n m p : ℕ}
    (f0 : (Fin n → ℝ) → ℝ)
    (f : Fin m → (Fin n → ℝ) → ℝ)
    (h : Fin p → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (nu : Fin p → ℝ) : ℝ :=
  f0 x + ∑ i : Fin m, lam i * f i x + ∑ j : Fin p, nu j * h j x

def DualVariables (m p : ℕ) : Set ((Fin m → ℝ) × (Fin p → ℝ)) :=
  {y | 0 ≤ y.1}

structure PrimalLogDetProblem (n m : ℕ) where
  a : Fin m → (Fin n → ℝ)
  b : Fin m → ℝ

def PrimalLogDetProblem.IsFeasible
    {n m : ℕ} (P : PrimalLogDetProblem n m)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ)
    (y : Fin m → (Fin n → ℝ)) : Prop :=
  B.IsSymm ∧
  (∀ i : Fin m, ‖y i‖ + ∑ j : Fin n, P.a i j * d j ≤ P.b i) ∧
  ∀ i : Fin m, (fun k : Fin n => ∑ j : Fin n, B k j * P.a i j) = y i

def PrimalLogDetProblem.objective
    {n m : ℕ} (P : PrimalLogDetProblem n m)
    (B : Matrix (Fin n) (Fin n) ℝ) : EReal :=
  if h : B.IsSymm ∧ 0 < Matrix.det B then
    ENNReal.toEReal (Real.toNNReal (-Real.log (Matrix.det B)))
  else
    ⊤

def PrimalLogDetProblem.constraintSet
    {n m : ℕ} (P : PrimalLogDetProblem n m) :
    Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) × (Fin m → (Fin n → ℝ))) :=
  {x | P.IsFeasible x.1 x.2.1 x.2.2}

theorem primal_log_det_dual_problem_formulation
    {n m : ℕ}
    (a : Fin m → (Fin n → ℝ))
    (b : Fin m → ℝ)
    (C : Set (Fin n → ℝ))
    (hC :
      C = {x | ∀ i : Fin m, (∑ j : Fin n, a i j * x j) ≤ b i})
    (hpoly : IsPolyhedron (n := n) C)
    (hnonempty : C.Nonempty)
    (hbounded : Bornology.IsBounded C) :
    let P : PrimalLogDetProblem n m := { a := a, b := b }
    ∃ f0 : (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
      ∃ f : Fin m → (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
        ∃ h : Fin (m * n) → (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
          LagrangeDualProblem f0 f h =
            { yz : (Fin m → ℝ) × (Fin (m * n) → ℝ) |
                (∀ i : Fin m, 0 ≤ yz.1 i) ∧
                let nu : Fin m → Fin n → ℝ :=
                  fun i j =>
                    yz.2 ((Fintype.equivFinOfCardEq (α := Fin m × Fin n) (by simp)) (i, j))
                let M : Matrix (Fin n) (Fin n) ℝ :=
                  fun r s => ∑ i : Fin m, nu i r * P.a i s
                (∀ i : Fin m, ‖nu i‖ ≤ yz.1 i) ∧
                (∀ j : Fin n, (∑ i : Fin m, yz.1 i * P.a i j) = 0) ∧
                M.IsSymm ∧ 0 < Matrix.det M ∧
                ∀ yz' : (Fin m → ℝ) × (Fin (m * n) → ℝ),
                  (∀ i : Fin m, 0 ≤ yz'.1 i) →
                  let nu' : Fin m → Fin n → ℝ :=
                    fun i j =>
                      yz'.2 ((Fintype.equivFinOfCardEq (α := Fin m × Fin n) (by simp)) (i, j))
                  let M' : Matrix (Fin n) (Fin n) ℝ :=
                    fun r s => ∑ i : Fin m, nu' i r * P.a i s
                  Real.log (Matrix.det M') + n - ∑ i : Fin m, P.b i * yz'.1 i ≤
                    Real.log (Matrix.det M) + n - ∑ i : Fin m, P.b i * yz.1 i } := by
  sorry

end «CAM-Bench-352»
