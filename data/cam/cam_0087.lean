import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-87»

def LinearIndependenceConstraintQualification
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (eqConstr : ι → E → ℝ) (ineqConstr : κ → E → ℝ) (x : E) : Prop :=
  LinearIndependent ℝ
    (fun z : {z : Sum ι κ |
        Sum.elim (fun i : ι => i ∈ (Set.univ : Set ι)) (fun j => ineqConstr j x = 0) z} =>
      Sum.elim
        (fun i : ι => gradient (eqConstr i) x)
        (fun j : κ => gradient (ineqConstr j) x)
        z.1)

def ActiveInequalityConstraint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Type*}
    (ineqConstr : κ → E → ℝ) (x : E) (j : κ) : Prop :=
  ineqConstr j x = 0

def ActiveSet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Type*}
    (ineqConstr : κ → E → ℝ) (x : E) : Set κ :=
  {j : κ | ActiveInequalityConstraint ineqConstr x j}

def FeasiblePoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (eqConstr : ι → E → ℝ) (ineqConstr : κ → E → ℝ) (x : E) : Prop :=
  (∀ i : ι, eqConstr i x = 0) ∧ ∀ j : κ, 0 ≤ ineqConstr j x

def SlackEqualityReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) : (E × (κ → ℝ)) → κ → ℝ :=
  fun xs j => ineqConstr j xs.1 - xs.2 j

def SlackVariableReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ j : κ, ineqConstr j xs.1 - xs.2 j = 0) ∧
  (∀ j : κ, 0 ≤ xs.2 j)

structure NonlinearProgramWithSlackReformulation
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type*) (κ : Type*) where
  objective : E → ℝ
  eqConstr : ι → E → ℝ
  ineqConstr : κ → E → ℝ
  objectiveContDiff : ContDiff ℝ ⊤ objective
  eqConstrContDiff : ∀ i : ι, ContDiff ℝ ⊤ (eqConstr i)
  ineqConstrContDiff : ∀ j : κ, ContDiff ℝ ⊤ (ineqConstr j)

def NonlinearProgramWithSlackReformulation.isFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (x : E) : Prop :=
  (∀ i : ι, P.eqConstr i x = 0) ∧ ∀ j : κ, 0 ≤ P.ineqConstr j x

def NonlinearProgramWithSlackReformulation.slackFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ i : ι, P.eqConstr i xs.1 = 0) ∧
    SlackVariableReformulation P.ineqConstr xs

theorem licq_iff_licq_slack_reformulation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    [hProdNormed : NormedAddCommGroup (E × (κ → ℝ))]
    [hProdInner : InnerProductSpace ℝ (E × (κ → ℝ))]
    (hProdComplete : @CompleteSpace (E × (κ → ℝ))
      (PseudoMetricSpace.toUniformSpace (α := E × (κ → ℝ))))
    (P : NonlinearProgramWithSlackReformulation E ι κ)
    (x : E)
    (s : κ → ℝ)
    (hx : P.isFeasible x)
    (hs : s = fun j => P.ineqConstr j x)
    (hxs : P.slackFeasible (x, s)) :
    LinearIndependenceConstraintQualification P.eqConstr P.ineqConstr x ↔
      @LinearIndependenceConstraintQualification
        (E × (κ → ℝ)) hProdNormed hProdInner hProdComplete (Sum ι κ) κ
        (fun ij : Sum ι κ => fun z : E × (κ → ℝ) =>
          Sum.elim
            (fun i => P.eqConstr i z.1)
            (fun j => SlackEqualityReformulation P.ineqConstr z j)
            ij)
        (fun j : κ => fun z : E × (κ → ℝ) => z.2 j)
        (x, s) := by
  sorry

end «CAM-Bench-87»
