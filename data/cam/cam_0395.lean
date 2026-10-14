import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-395»

def StrictlyFeasible {m n : Type} [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  A.mulVec x = b ∧ ∀ i : n, 0 < x i

structure BarrierSubproblem (m n : Type) [Fintype n] where
  A : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ
  φ : (n → ℝ) → ℝ
  t : ℝ
  t_pos : 0 < t

def BarrierSubproblem.domain {m n : Type} [Fintype n]
    (_P : BarrierSubproblem m n) : Set (n → ℝ) :=
  {x | ∀ i : n, 0 < x i}

def BarrierSubproblem.feasibleSet {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) : Set (n → ℝ) :=
  {x | P.A.mulVec x = P.b ∧ x ∈ P.domain}

def BarrierSubproblem.objective {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) : (n → ℝ) → ℝ :=
  fun x => P.t * dotProduct P.c x + P.φ x

def BarrierSubproblem.IsMinimizer {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) (x : n → ℝ) : Prop :=
  x ∈ P.feasibleSet ∧ ∀ y, y ∈ P.feasibleSet → P.objective x ≤ P.objective y

def NewtonDecrement {n : Type} [Fintype n] [DecidableEq n]
    (φHess : (n → ℝ) → Matrix n n ℝ) (x Δx : n → ℝ) : ℝ :=
  Real.sqrt (dotProduct Δx ((φHess x).mulVec Δx))

def DualFeasible {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  ∀ i : n, ((Matrix.transpose A).mulVec y) i ≤ c i

def IsBarrierFunction {α : Type} [TopologicalSpace α] (interiorSet : Set α) (φ : α → WithTop ℝ) : Prop :=
  (∀ x, x ∈ interiorSet → ∃ r : ℝ, φ x = (r : WithTop ℝ)) ∧
  ∀ y ∈ frontier interiorSet, Tendsto φ (nhdsWithin y interiorSet) atTop

def LogarithmicBarrierDomain {n : Type} [Fintype n] (x : n → ℝ) : Prop :=
  ∀ i : n, 0 < x i

structure BarrierFunctionWithDomain (n : Type) where
  domain : Set (n → ℝ)
  toFun : {x : n → ℝ // x ∈ domain} → ℝ

instance {n : Type} : CoeFun (BarrierFunctionWithDomain n) (fun _ => (n → ℝ) → ℝ) where
  coe φ x := by
    classical
    exact if hx : x ∈ φ.domain then φ.toFun ⟨x, hx⟩ else 0

def LogarithmicBarrier {n : Type} [Fintype n] : BarrierFunctionWithDomain n where
  domain := {x | LogarithmicBarrierDomain x}
  toFun := fun x => -∑ i : n, Real.log (x.1 i)

structure PrimalDualLinearProgram (m n : Type) [Fintype m] [Fintype n] where
  A : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ
  rank_eq : A.rank = Fintype.card m
  strictly_feasible_point : n → ℝ
  strictly_feasible : StrictlyFeasible A b strictly_feasible_point

def PrimalDualLinearProgram.primalFeasible {m n : Type} [Fintype m] [Fintype n]
    (P : PrimalDualLinearProgram m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b ∧ ∀ i : n, 0 ≤ x i

def PrimalDualLinearProgram.dualFeasible {m n : Type} [Fintype m] [Fintype n]
    (P : PrimalDualLinearProgram m n) (y : m → ℝ) : Prop :=
  DualFeasible P.A P.c y

def PrimalDualLinearProgram.primalObjective {m n : Type} [Fintype m] [Fintype n]
    (P : PrimalDualLinearProgram m n) (x : n → ℝ) : ℝ :=
  dotProduct P.c x

def PrimalDualLinearProgram.dualObjective {m n : Type} [Fintype m] [Fintype n]
    (P : PrimalDualLinearProgram m n) (y : m → ℝ) : ℝ :=
  dotProduct P.b y

structure LogBarrierSubproblem (m n : Type) [Fintype n] where
  A : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ
  t : ℝ
  t_pos : 0 < t

def LogBarrierSubproblem.toBarrierSubproblem {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) : BarrierSubproblem m n :=
  { A := P.A
    b := P.b
    c := P.c
    φ := LogarithmicBarrier
    t := P.t
    t_pos := P.t_pos }

def LogBarrierSubproblem.feasibleSet {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) : Set (n → ℝ) :=
  P.toBarrierSubproblem.feasibleSet ∩ P.toBarrierSubproblem.domain

def LogBarrierSubproblem.objective {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) (x : n → ℝ) : ℝ :=
  P.toBarrierSubproblem.objective x

def LogBarrierSubproblem.isInDomain {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) (x : n → ℝ) : Prop :=
  x ∈ P.toBarrierSubproblem.domain

theorem scaled_newton_dual_variable_dualFeasible
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : PrimalDualLinearProgram m n) (B : LogBarrierSubproblem m n)
    (xhat dx : n → ℝ) (w : m → ℝ)
      (h_base :
        B.A = P.A ∧
        B.b = P.b ∧
        B.c = P.c)
    (hxhat : StrictlyFeasible P.A P.b xhat)
    (hNewton1 :
        (Matrix.diagonal (fun i => 1 / (xhat i) ^ 2)).mulVec dx +
          (Matrix.transpose P.A).mulVec w =
        fun i => - (B.t * P.c i - 1 / xhat i))
    (hNewton2 : P.A.mulVec dx = 0)
    (hdecr : NewtonDecrement (fun x => Matrix.diagonal (fun i => 1 / (x i) ^ 2)) xhat dx ≤ 1) :
      DualFeasible P.A P.c (- (1 / B.t) • w) := by
  sorry

end «CAM-Bench-395»
