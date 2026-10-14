import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-688»

def IsFeasible {α : Type*} (constraints : Set α) (x : α) : Prop :=
  x ∈ constraints

def euclideanLength {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

structure RestrictedConvexProblem (k N m : ℕ) where
  f0 : (Fin N → Fin k → ℝ) → ℝ
  fi : Fin m → (Fin N → Fin k → ℝ) → ℝ
  a : ∀ (i j : Fin N), Fin k → ℝ
  unit_norm : ∀ {i j : Fin N}, i.val < j.val → euclideanLength (a i j) = 1
  Dmin : ℝ

def RestrictedConvexProblem.constraints {k N m : ℕ} (P : RestrictedConvexProblem k N m) :
    Set (Fin N → Fin k → ℝ) :=
  {x | (∀ i : Fin m, P.fi i x ≤ 0) ∧
      ∀ i j : Fin N, i.val < j.val → ∑ t : Fin k, P.a i j t * (x i t - x j t) ≥ P.Dmin}

def RestrictedConvexProblem.isFeasible {k N m : ℕ} (P : RestrictedConvexProblem k N m)
    (x : Fin N → Fin k → ℝ) : Prop :=
  IsFeasible P.constraints x

def RestrictedConvexProblem.objectiveValue {k N m : ℕ} (P : RestrictedConvexProblem k N m)
    (x : Fin N → Fin k → ℝ) : ℝ :=
  P.f0 x

theorem restrictedConvexProblem_feasible_implies_min_distance
    {k N m : ℕ} (P : RestrictedConvexProblem k N m)
    (hconv_f0 : ConvexOn ℝ (Set.univ : Set (Fin N → Fin k → ℝ)) P.f0)
    (hconv_fi : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin N → Fin k → ℝ)) (P.fi i)) :
    Convex ℝ P.constraints ∧
      ∀ x : Fin N → Fin k → ℝ, P.isFeasible x →
        ∀ i j : Fin N, i.val < j.val → euclideanLength (x i - x j) ≥ P.Dmin := by
  sorry

end «CAM-Bench-688»
