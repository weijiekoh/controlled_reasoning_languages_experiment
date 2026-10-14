import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-396»

instance {n : ℕ} : Coe (Fin n → ℝ) ((Fin n → ℝ) → ℝ) where
  coe := fun c x => dotProduct c x

structure BarrierSubproblemData
    {n p : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ)
    (φ : (Fin n → ℝ) → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ)
      (b : Fin p → ℝ)
      (t : ℝ) where
    domφ : Set (Fin n → ℝ)
    t_pos : 0 < t

def BarrierSubproblemData.feasibleSet
    {n p : ℕ}
    {f₀ : (Fin n → ℝ) → ℝ}
    {φ : (Fin n → ℝ) → ℝ}
    {A : Matrix (Fin p) (Fin n) ℝ}
    {b : Fin p → ℝ}
    {t : ℝ}
    (S : BarrierSubproblemData f₀ φ A b t) : Set (Fin n → ℝ) :=
  {x | A.mulVec x = b ∧ x ∈ S.domφ}

def BarrierSubproblemData.objective
    {n p : ℕ}
    {f₀ : (Fin n → ℝ) → ℝ}
    {φ : (Fin n → ℝ) → ℝ}
    {A : Matrix (Fin p) (Fin n) ℝ}
    {b : Fin p → ℝ}
    {t : ℝ}
    (_S : BarrierSubproblemData f₀ φ A b t) : (Fin n → ℝ) → ℝ :=
  fun x => t * f₀ x + φ x

instance {n p : ℕ}
    {f₀ : (Fin n → ℝ) → ℝ}
    {φ : (Fin n → ℝ) → ℝ}
    {A : Matrix (Fin p) (Fin n) ℝ}
    {b : Fin p → ℝ}
    {t : ℝ} :
    CoeHead (BarrierSubproblemData f₀ φ A b t) (Set (Fin n → ℝ)) where
  coe := fun S => S.feasibleSet

def strictlyFeasiblePoint
    {n p : ℕ}
    (A : Matrix (Fin p) (Fin n) ℝ)
    (b : Fin p → ℝ) : Set (Fin n → ℝ) :=
  {x | A.mulVec x = b ∧ ∀ i : Fin n, 0 < x i}

open scoped BigOperators

def newtonDecrement
    {n : ℕ}
    (φHess : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x Δx : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct Δx ((φHess x).mulVec Δx))

structure PrimalDualLinearProgram where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  rank_eq : Module.finrank ℝ (LinearMap.range A.toLin') = m

def StrictlyFeasiblePoint {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A.mulVec x = b ∧ ∀ i : Fin n, 0 < x i

def BarrierSubproblem {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (t : ℝ) (_c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  0 < t ∧ A.mulVec x = b ∧ (∀ i : Fin n, 0 < x i)

def PrimalDualLinearProgram.primalFeasibleSet (P : PrimalDualLinearProgram) : Set (Fin P.n → ℝ) :=
  StrictlyFeasiblePoint P.A P.b

def PrimalDualLinearProgram.primalObjective (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  dotProduct P.c x

def PrimalDualLinearProgram.dualFeasibleSet (P : PrimalDualLinearProgram) : Set (Fin P.m → ℝ) :=
  {y | ∀ j : Fin P.n, ((P.A.transpose).mulVec y) j ≤ P.c j}

def PrimalDualLinearProgram.dualObjective (P : PrimalDualLinearProgram) (y : Fin P.m → ℝ) : ℝ :=
  dotProduct P.b y

def PrimalDualLinearProgram.barrierProblem (P : PrimalDualLinearProgram) (t : ℝ) : Set (Fin P.n → ℝ) :=
  BarrierSubproblem P.A P.b t P.c

structure LogBarrierSubproblem where
  P : PrimalDualLinearProgram
  t : ℝ
  t_pos : 0 < t

def LogBarrierSubproblem.phi (S : LogBarrierSubproblem) : (Fin S.P.n → ℝ) → ℝ :=
  fun x => -∑ i : Fin S.P.n, Real.log (x i)

def LogBarrierSubproblem.domain (S : LogBarrierSubproblem) : Set (Fin S.P.n → ℝ) :=
  {x | ∀ i : Fin S.P.n, 0 < x i}

def LogBarrierSubproblem.objective (S : LogBarrierSubproblem) : (Fin S.P.n → ℝ) → ℝ :=
  fun x => S.t * dotProduct S.P.c x + S.phi x

def LogBarrierSubproblem.feasibleSet (S : LogBarrierSubproblem) : Set (Fin S.P.n → ℝ) :=
  {x | S.P.A.mulVec x = S.P.b ∧ x ∈ S.domain}

theorem logBarrier_suboptimality_bound
    (S : LogBarrierSubproblem)
    (pStar : ℝ)
    (hpStar :
      IsLeast
        {v : ℝ | ∃ x : Fin S.P.n → ℝ,
            x ∈ S.P.primalFeasibleSet ∧
            v = S.P.primalObjective x}
        pStar)
    (xhat : Fin S.P.n → ℝ)
    (hfeas : xhat ∈ S.domain)
    (hxeq : S.P.A.mulVec xhat = S.P.b)
    (dx : Fin S.P.n → ℝ)
    (w : Fin S.P.m → ℝ)
    (hNewton :
      (Matrix.diagonal (fun i : Fin S.P.n => 1 / (xhat i)^2)).mulVec dx + S.P.A.transpose.mulVec w =
        (fun i : Fin S.P.n => -S.t * S.P.c i + 1 / xhat i) ∧
      S.P.A.mulVec dx = 0)
    (hlam :
      newtonDecrement
        (fun x : Fin S.P.n → ℝ => Matrix.diagonal (fun i : Fin S.P.n => 1 / (x i)^2))
        xhat dx ≤ 1) :
    dotProduct S.P.c xhat - pStar ≤
      ((S.P.n : ℝ) +
        newtonDecrement
          (fun x : Fin S.P.n → ℝ => Matrix.diagonal (fun i : Fin S.P.n => 1 / (x i)^2))
          xhat dx * Real.sqrt S.P.n) / S.t := by
  sorry

end «CAM-Bench-396»
