import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-320»

def lagrangeDualFunction {X Lam : Type*} (L : X → Lam → ℝ) : Lam → EReal :=
  fun lam => sInf (Set.range fun x : X => (L x lam : EReal))

def LagrangeDualProblem {X Lam : Type*} (L : X → Lam → ℝ) (admissible : Set Lam) : Set Lam :=
  {lam | lam ∈ admissible ∧ ∀ μ, μ ∈ admissible → lagrangeDualFunction L μ ≤ lagrangeDualFunction L lam}

def DualVariable {X Lam : Type*} [SMul Lam Lam] (h : X → Lam) (ν : Lam) :
    X → Lam :=
  fun x => ν • h x

open scoped BigOperators

structure L2L1PrimalProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  γ : ℝ

def L2L1PrimalProblem.objective
    (P : L2L1PrimalProblem) : ((Fin P.n → ℝ) × (Fin P.m → ℝ)) → ℝ :=
  fun p => ‖p.2‖ + P.γ * ‖p.1‖

def L2L1PrimalProblem.feasibleSet
    (P : L2L1PrimalProblem) : Set ((Fin P.n → ℝ) × (Fin P.m → ℝ)) :=
  {p | P.A.mulVec p.1 - P.b = p.2}

theorem l2l1_primalProblem_has_lagrangeDual
    (p : L2L1PrimalProblem) (hγ : 0 < p.γ) :

    ∀ ν : Fin p.m → ℝ,
      ‖ν‖ ≤ 1 →
      (∀ j : Fin p.n, |(Matrix.mulVec p.Aᵀ ν) j| ≤ p.γ) →
      lagrangeDualFunction
        (fun xy : (Fin p.n → ℝ) × (Fin p.m → ℝ) => fun ν : Fin p.m → ℝ =>
          ‖xy.2‖ + p.γ * ‖xy.1‖ + ∑ i : Fin p.m, ν i * ((p.A.mulVec xy.1 - p.b - xy.2) i))
        ν =
      (-∑ i : Fin p.m, p.b i * ν i : ℝ) := by
  sorry

end «CAM-Bench-320»
