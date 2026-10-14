import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-330»

def Lagrangian {X : Type*} {m : ℕ} (f0 : X → ℝ) (f : Fin m → X → ℝ) :
    X → (Fin m → ℝ) → ℝ :=
  fun x lam => f0 x + ∑ i, lam i * f i x

def dualFunction {m : ℕ} (f0 : ℝ → ℝ) (f : Fin m → ℝ → ℝ) : (Fin m → ℝ) → EReal :=
  fun lam => sInf (Set.range fun x : ℝ => (Lagrangian f0 f x lam : EReal))

def primalProblem (P : Set ℝ) : Set ℝ := P

def optimalValue (f : ℝ → ℝ) (C : Set ℝ) : EReal :=
  sInf (((fun x => (f x : EReal)) '' C) : Set EReal)

structure ConvexInequalityConstrainedProblem (m : ℕ) where
  n : ℕ
  f0 : (Fin n → ℝ) → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ
  f0_diff : Differentiable ℝ f0
  f_diff : ∀ i, Differentiable ℝ (f i)
  f0_convex : ConvexOn ℝ Set.univ f0
  f_convex : ∀ i, ConvexOn ℝ Set.univ (f i)

def ConvexInequalityConstrainedProblem.feasibleSet {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : Set (Fin P.n → ℝ) :=
  {x | ∀ i, P.f i x ≤ 0}

def ConvexInequalityConstrainedProblem.objectiveValue {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : EReal :=
  sInf (((fun x => (P.f0 x : EReal)) '' ConvexInequalityConstrainedProblem.feasibleSet P) : Set EReal)

def ConvexInequalityConstrainedProblem.lagrangian {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : (Fin P.n → ℝ) → (Fin m → ℝ) → ℝ :=
  Lagrangian P.f0 P.f

def ConvexInequalityConstrainedProblem.dualFunction {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : (Fin m → ℝ) → EReal :=
  fun lam => sInf (Set.range fun x : Fin P.n → ℝ => (Lagrangian P.f0 P.f x lam : EReal))

def ConvexInequalityConstrainedProblem.primalSet {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : Set (Fin P.n → ℝ) :=
  ConvexInequalityConstrainedProblem.feasibleSet P

theorem penalty_minimizer_yields_dual_lower_bound
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m) (alpha : ℝ) (xtilde : Fin P.n → ℝ)
    (halpha : 0 < alpha)
    (hxtilde_min :
      IsLeast (Set.range (fun x : Fin P.n → ℝ => P.f0 x + alpha * ∑ i, max 0 (P.f i x) ^ (2 : ℕ)))
        (P.f0 xtilde + alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ))) :
    ConvexOn ℝ Set.univ
      (fun x => P.f0 x + alpha * ∑ i, max 0 (P.f i x) ^ (2 : ℕ)) ∧
    (∀ i, 0 ≤ (2 * alpha * max 0 (P.f i xtilde))) ∧
    IsLeast
      (Set.range
        (fun x : Fin P.n → ℝ =>
          (Lagrangian P.f0 P.f x (fun i => 2 * alpha * max 0 (P.f i xtilde)) : ℝ)))
      (Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde))) ∧

    (P.dualFunction (fun i => 2 * alpha * max 0 (P.f i xtilde)) =
      (Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde)) : EReal)) ∧
    ((Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde)) : EReal) =
      (P.f0 xtilde + 2 * alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ) : EReal)) ∧

    P.objectiveValue ≥ P.dualFunction (fun i => 2 * alpha * max 0 (P.f i xtilde)) ∧
    P.objectiveValue ≥
      (P.f0 xtilde + 2 * alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ) : EReal) := by
  sorry

end «CAM-Bench-330»
