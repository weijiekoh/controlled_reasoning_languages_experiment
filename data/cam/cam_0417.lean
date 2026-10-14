import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-417»

structure NonlinearConstrainedProblem (n m p : ℕ) where
  f : Fin (m + 1) → (Fin n → ℝ) → ℝ
  A : Fin p → Fin n → ℝ
  b : Fin p → ℝ
  t : ℝ
  t_pos : 0 < t

def NonlinearConstrainedProblem.f0 {n m p : ℕ}
    (P : NonlinearConstrainedProblem n m p) : (Fin n → ℝ) → ℝ :=
  P.f 0

def NonlinearConstrainedProblem.fi {n m p : ℕ}
    (P : NonlinearConstrainedProblem n m p) : Fin m → (Fin n → ℝ) → ℝ :=
  fun i => P.f i.succ

def NonlinearConstrainedProblem.IsFeasible {n m p : ℕ}
    (P : NonlinearConstrainedProblem n m p) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, P.fi i x ≤ 0) ∧
    ∀ j : Fin p, ∑ k : Fin n, P.A j k * x k = P.b j

def NonlinearConstrainedProblem.ObjectiveValue {n m p : ℕ}
    (P : NonlinearConstrainedProblem n m p) (x : Fin n → ℝ) : ℝ :=
  P.f0 x

structure CenteringProblem (n m p : ℕ) where
  base : NonlinearConstrainedProblem n m p

def CenteringProblem.logBarrier {n m p : ℕ}
    (P : CenteringProblem n m p) (x : Fin n → ℝ) : ℝ :=
  -∑ i : Fin m, Real.log (-P.base.fi i x)

def CenteringProblem.barrierDomain {n m p : ℕ}
    (P : CenteringProblem n m p) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin m, P.base.fi i x < 0}

def CenteringProblem.objectiveValue {n m p : ℕ}
    (P : CenteringProblem n m p) (x : Fin n → ℝ) : ℝ :=
  P.base.t * P.base.f0 x + P.logBarrier x

def CenteringProblem.IsFeasible {n m p : ℕ}
    (P : CenteringProblem n m p) (x : Fin n → ℝ) : Prop :=
  x ∈ P.barrierDomain ∧
    ∀ j : Fin p, ∑ k : Fin n, P.base.A j k * x k = P.base.b j

theorem centering_sublevel_bounded_of_base_sublevel_bounded
    {n m p : ℕ} (P : CenteringProblem n m p)
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          {x : Fin n → ℝ |
            NonlinearConstrainedProblem.IsFeasible P.base x ∧
            P.base.f0 x ≤ α})
    (hbarrier_bddBelow :
      ∃ L : ℝ, ∀ x : Fin n → ℝ, CenteringProblem.IsFeasible P x → L ≤ P.logBarrier x) :
    ∀ β : ℝ,
      Bornology.IsBounded
        {x : Fin n → ℝ |
          CenteringProblem.IsFeasible P x ∧
          P.objectiveValue x ≤ β} := by
  sorry

end «CAM-Bench-417»
