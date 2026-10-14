import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-419»

def IsClosedExtendedRealFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsClosed {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

structure RestrictedNegFunction where
  n : ℕ
  m : ℕ
  domain : Set (Fin n → ℝ)
  convex_domain : Convex ℝ domain
  h : ℝ → ℝ
  h_twiceDifferentiable : ContDiffOn ℝ 2 h (Set.Iio 0)
  h_closed : IsClosed {p : ℝ × ℝ | p.1 < 0 ∧ h p.1 ≤ p.2}
  h_increasing : MonotoneOn h (Set.Iio 0)
  h_convex : ConvexOn ℝ (Set.Iio 0) h
  f : Fin (m + 1) → (Fin n → ℝ) → ℝ
  f_twiceDifferentiable : ∀ i : Fin (m + 1), ContDiffOn ℝ 2 (f i) domain
  f_convex : ∀ i : Fin (m + 1), ConvexOn ℝ domain (f i)

instance : CoeFun RestrictedNegFunction (fun _ => ℝ → ℝ) where
  coe h := h.h

structure ConvexInequalityConstrainedProblem where
  n : ℕ
  m : ℕ
  domain : Set (Fin n → ℝ)
  convex_domain : Convex ℝ domain
  h : ℝ → ℝ
  h_twiceDifferentiable : ContDiffOn ℝ 2 h (Set.Iio 0)
  h_closed : IsClosed {p : ℝ × ℝ | p.1 < 0 ∧ h p.1 ≤ p.2}
  h_increasing : MonotoneOn h (Set.Iio 0)
  h_convex : ConvexOn ℝ (Set.Iio 0) h
  f0 : (Fin n → ℝ) → ℝ
  constraints : Fin m → (Fin n → ℝ) → ℝ
  f0_twiceDifferentiable : ContDiffOn ℝ 2 f0 domain
  constraints_twiceDifferentiable : ∀ i : Fin m, ContDiffOn ℝ 2 (constraints i) domain
  f0_convex : ConvexOn ℝ domain f0
  constraints_convex : ∀ i : Fin m, ConvexOn ℝ domain (constraints i)

def ConvexInequalityConstrainedProblem.f
    (P : ConvexInequalityConstrainedProblem) (i : Fin (P.m + 1)) (x : Fin P.n → ℝ) :
    ℝ := by
  by_cases h0 : i.1 = 0
  · exact P.f0 x
  · exact
      P.constraints
        ⟨i.1 - 1, by
          have hi_lt : i.1 < P.m + 1 := i.2
          have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero h0
          omega⟩
        x

def ConvexInequalityConstrainedProblem.isFeasible
    (P : ConvexInequalityConstrainedProblem) (x : Fin P.n → ℝ) : Prop :=
  x ∈ P.domain ∧ ∀ i : Fin P.m, P.f i.succ x ≤ 0

def ConvexInequalityConstrainedProblem.objective
    (P : ConvexInequalityConstrainedProblem) (x : Fin P.n → ℝ) : ℝ :=
  P.f0 x

structure BarrierSubproblem where
  problem : ConvexInequalityConstrainedProblem

def BarrierSubproblem.barrierObjective
    (B : BarrierSubproblem) (t : ℝ) (x : Fin B.problem.n → ℝ) : ℝ :=
  t * B.problem.objective x + ∑ i : Fin B.problem.m, B.problem.h (B.problem.f i.succ x)

def BarrierSubproblem.isMinimizer
    (B : BarrierSubproblem) (t : ℝ) (x : Fin B.problem.n → ℝ) : Prop :=
  x ∈ B.problem.domain ∧
    (∀ i : Fin B.problem.m, B.problem.f i.succ x < 0) ∧
    ∀ y : Fin B.problem.n → ℝ,
      y ∈ B.problem.domain →
        (∀ i : Fin B.problem.m, B.problem.f i.succ y < 0) →
        B.barrierObjective t x ≤ B.barrierObjective t y

theorem barrierObjective_convex_on_barrierDomain
    (B : BarrierSubproblem) :
    ∀ t : ℝ, 0 < t →
      ConvexOn ℝ
        {x : Fin B.problem.n → ℝ |
          x ∈ B.problem.domain ∧ ∀ i : Fin B.problem.m, B.problem.f i.succ x < 0}
        (fun x => B.barrierObjective t x) := by
  sorry

end «CAM-Bench-419»
