import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-210»

structure ConvexSchedulingProblem where
  n : ℕ
  T : ℕ
  φ : ℝ → ℝ
  A : Fin n → ℕ
  D : Fin n → ℕ
  W : Fin n → ℝ
  s_min : ℝ
  s_max : ℝ
  R : ℝ
  x : Fin n → Fin T → ℝ

def ConvexSchedulingProblem.totalLoad (p : ConvexSchedulingProblem) (t : Fin p.T) : ℝ :=
  ∑ i : Fin p.n, p.x i t

def ConvexSchedulingProblem.objective (p : ConvexSchedulingProblem) : ℝ :=
  ∑ t : Fin p.T, p.φ (p.totalLoad t)

def ConvexSchedulingProblem.jobDeliveredEnergy (p : ConvexSchedulingProblem) (i : Fin p.n) : ℝ :=
  ∑ t : Fin p.T, p.x i t

def ConvexSchedulingProblem.respectsAvailability (p : ConvexSchedulingProblem) : Prop :=
  ∀ i : Fin p.n, ∀ t : Fin p.T, (t.1 + 1 < p.A i ∨ p.D i < t.1 + 1) → p.x i t = 0

def ConvexSchedulingProblem.meetsWorkDemand (p : ConvexSchedulingProblem) : Prop :=
  ∀ i : Fin p.n, p.W i ≤ p.jobDeliveredEnergy i

def ConvexSchedulingProblem.respectsLoadBounds (p : ConvexSchedulingProblem) : Prop :=
  ∀ t : Fin p.T, p.s_min ≤ p.totalLoad t ∧ p.totalLoad t ≤ p.s_max

def ConvexSchedulingProblem.respectsRampLimit (p : ConvexSchedulingProblem) : Prop :=
  ∀ t : Fin (p.T - 1),
    ∃ hnext : t.1 + 1 < p.T,
      |p.totalLoad ⟨t.1 + 1, hnext⟩ - p.totalLoad ⟨t.1, Nat.lt_of_lt_of_le t.isLt (Nat.sub_le _ _)⟩| ≤ p.R

def ConvexSchedulingProblem.nonnegative (p : ConvexSchedulingProblem) : Prop :=
  ∀ i : Fin p.n, ∀ t : Fin p.T, 0 ≤ p.x i t

def ConvexSchedulingProblem.isFeasible (p : ConvexSchedulingProblem) : Prop :=
  p.respectsAvailability ∧
    p.meetsWorkDemand ∧
    p.respectsLoadBounds ∧
    p.respectsRampLimit ∧
    p.nonnegative

theorem scheduling_problem_equivalent_to_convex_scheduling
    (p : ConvexSchedulingProblem)
    (hφ_mono : Monotone p.φ)
    (hφ_convex : ConvexOn ℝ Set.univ p.φ)
    (hA_le_D : ∀ i : Fin p.n, p.A i ≤ p.D i)
    (hW_nonneg : ∀ i : Fin p.n, 0 ≤ p.W i)
    (hs_min_pos : 0 < p.s_min)
    (hR_nonneg : 0 ≤ p.R)
    (hcover : ∀ t : Fin p.T, ∃ i : Fin p.n, p.A i ≤ t.1 + 1 ∧ t.1 + 1 ≤ p.D i) :
    p.isFeasible →
      ∃ s : Fin p.T → ℝ,
        ∃ θ : Fin p.n → Fin p.T → ℝ,
          (∀ t : Fin p.T, s t = p.totalLoad t) ∧
          (∀ i : Fin p.n, ∀ t : Fin p.T, θ i t = p.x i t / s t) ∧
          (∀ t : Fin p.T, 0 < s t) ∧
          (∀ t : Fin p.T, ∑ i : Fin p.n, θ i t = 1) ∧
          (∀ i : Fin p.n, ∀ t : Fin p.T, 0 ≤ θ i t) ∧
          (∀ i : Fin p.n, ∀ t : Fin p.T,
            (t.1 + 1 < p.A i ∨ p.D i < t.1 + 1) → θ i t = 0) ∧
          (∀ i : Fin p.n, ∑ t : Fin p.T, θ i t * s t ≥ p.W i) ∧
          (∑ t : Fin p.T, p.φ (s t) = p.objective) := by
  sorry

end «CAM-Bench-210»
