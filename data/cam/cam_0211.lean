import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-211»

def nodeEdgeIncidenceMatrix (n m : ℕ) (tail head : Fin m → Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j =>
    if tail j = i then
      1
    else if head j = i then
      -1
    else
      0

def IsOptimalSolution {α β : Type*} [Preorder β] (f : α → β) (feasible : Set α) (xStar : α) : Prop :=
  xStar ∈ feasible ∧ ∀ x ∈ feasible, f xStar ≤ f x

def IsOptimalDualVariable {Λ β : Type*} [Preorder β]
    (dualObjective : Λ → β) (dualFeasible : Set Λ) (lambdaStar : Λ) : Prop :=
  lambdaStar ∈ dualFeasible ∧ ∀ lam ∈ dualFeasible, dualObjective lam ≤ dualObjective lambdaStar

def lagrangian
    {α ιg ιh : Type*}
    [Fintype ιg] [Fintype ιh]
    (f : α → ℝ)
    (g : α → ιg → ℝ)
    (h : α → ιh → ℝ)
    (x : α)
    (lambda : ιg → ℝ)
    (nu : ιh → ℝ) : ℝ :=
  f x + ∑ i, lambda i * g x i + ∑ j, nu j * h x j

def effectiveDomain {α : Type*} (f : α → EReal) : Set α :=
  {x | f x < ⊤}

open scoped BigOperators

structure NetworkFlowConvexProgram where
  n : ℕ
  m : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n
  s : Fin n → ℝ
  kappa : Fin m → ℝ
  kappa_pos : ∀ j, 0 < kappa j

def NetworkFlowConvexProgram.A (P : NetworkFlowConvexProgram) : Matrix (Fin P.n) (Fin P.m) ℝ :=
  nodeEdgeIncidenceMatrix P.n P.m P.tail P.head

def NetworkFlowConvexProgram.psi (P : NetworkFlowConvexProgram) (j : Fin P.m) (u : ℝ) : ℝ :=
  u * Real.arcsin (u / P.kappa j) + P.kappa j * (Real.sqrt (1 - (u / P.kappa j) ^ 2) - 1)

def NetworkFlowConvexProgram.psiDom (P : NetworkFlowConvexProgram) (j : Fin P.m) : Set ℝ :=
  Set.Ioo (-P.kappa j) (P.kappa j)

def NetworkFlowConvexProgram.feasible (P : NetworkFlowConvexProgram) (p : Fin P.m → ℝ) : Prop :=
  P.A.mulVec p = P.s

def NetworkFlowConvexProgram.inDomain (P : NetworkFlowConvexProgram) (p : Fin P.m → ℝ) : Prop :=
  ∀ j, p j ∈ P.psiDom j

def NetworkFlowConvexProgram.objective (P : NetworkFlowConvexProgram) (p : Fin P.m → ℝ) : ℝ :=
  ∑ j, P.psi j (p j)

def NetworkFlowConvexProgram.isFeasible (P : NetworkFlowConvexProgram) (p : Fin P.m → ℝ) : Prop :=
  P.feasible p ∧ P.inDomain p

theorem optimal_flow_satisfies_dc_power_flow
    (P : NetworkFlowConvexProgram)
    (h_feas : ∃ p : Fin P.m → ℝ, P.feasible p ∧ P.inDomain p)
    (pStar : Fin P.m → ℝ)
    (uStar : Fin P.n → ℝ)
    (h_pStar_opt : IsOptimalSolution P.objective {p | P.isFeasible p} pStar)
    (h_uStar_opt :
      IsOptimalDualVariable
        (fun u : Fin P.n → ℝ =>
          sInf
            {r : ℝ | ∃ p : Fin P.m → ℝ,
              P.inDomain p ∧
              r = P.objective p + u ⬝ᵥ P.A.mulVec p})
        (Set.univ : Set (Fin P.n → ℝ))
        uStar) :
    P.A.mulVec pStar = P.s ∧
    pStar = fun j => P.kappa j * Real.sin (((P.A.transpose.mulVec (-uStar)) j)) := by
  sorry

end «CAM-Bench-211»
