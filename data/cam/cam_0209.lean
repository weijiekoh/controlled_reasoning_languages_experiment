import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-209»

def IsAcyclicDigraph {V : Type*} (E : V → V → Prop) : Prop :=
  ¬ ∃ (k : ℕ) (_hk : 0 < k) (v : Fin (k + 1) → V),
    (∀ i j, i ≠ j → v i ≠ v j) ∧
    (∀ i : Fin k, E (v (Fin.castSucc i)) (v (Fin.succ i))) ∧
    E (v (Fin.last k)) (v 0)

structure PrecedenceConstrainedSchedulingProblem where
  n : ℕ
  α : Fin n → ℝ
  sMin : ℝ
  sMax : ℝ
  sMin_pos : 0 < sMin
  sMax_pos : 0 < sMax
  sMin_le_sMax : sMin ≤ sMax
  f : ℝ → ℝ
  precedence : Fin n → Fin n → Prop
  Emax : ℝ
  τ : Fin n → ℝ
  t : Fin n → ℝ
  T : ℝ
  tau_pos : ∀ i, 0 < τ i
  tau_lower : ∀ i, α i / sMax ≤ τ i
  tau_upper : ∀ i, τ i ≤ α i / sMin
  start_nonneg : ∀ i, 0 ≤ t i
  precedence_constraint : ∀ i j, precedence i j → t j ≥ t i + τ i
  completion_bound : ∀ i, T ≥ t i + τ i
  energy_constraint : (∑ i, τ i * f (α i / τ i)) ≤ Emax

def PrecedenceConstrainedSchedulingProblem.objective
    (p : PrecedenceConstrainedSchedulingProblem) : ℝ :=
  p.T

def PrecedenceConstrainedSchedulingProblem.is_feasible
    (p : PrecedenceConstrainedSchedulingProblem) : Prop :=
  (∀ i, 0 < p.τ i) ∧
  (∀ i, p.α i / p.sMax ≤ p.τ i) ∧
  (∀ i, p.τ i ≤ p.α i / p.sMin) ∧
  (∀ i, 0 ≤ p.t i) ∧
  (∀ i j, p.precedence i j → p.t j ≥ p.t i + p.τ i) ∧
  (∀ i, p.T ≥ p.t i + p.τ i) ∧
  (∑ i, p.τ i * p.f (p.α i / p.τ i)) ≤ p.Emax

theorem precedenceConstrainedSchedulingProblem_isConvexOptimization
    (p : PrecedenceConstrainedSchedulingProblem)
    (hn : 1 ≤ p.n)
    (hacyclic : IsAcyclicDigraph p.precedence)
    (hs : 0 < p.sMin ∧ p.sMin ≤ p.sMax)
    (hα : ∀ i, 0 < p.α i)
    (hf_pos : ∀ x ∈ Set.Icc p.sMin p.sMax, 0 < p.f x)
    (hf_mono : MonotoneOn p.f (Set.Icc p.sMin p.sMax))
    (hf_convex : ConvexOn ℝ (Set.Icc p.sMin p.sMax) p.f) :
    let feasibleSet : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ) × ℝ) :=
      {x |
        (∀ i, 0 < x.1 i) ∧
        (∀ i, p.α i / p.sMax ≤ x.1 i) ∧
        (∀ i, x.1 i ≤ p.α i / p.sMin) ∧
        (∀ i, 0 ≤ x.2.1 i) ∧
        (∀ i j, p.precedence i j → x.2.1 j ≥ x.2.1 i + x.1 i) ∧
        (∀ i, x.2.2 ≥ x.2.1 i + x.1 i) ∧
        (∑ i, x.1 i * p.f (p.α i / x.1 i)) ≤ p.Emax}
    Convex ℝ feasibleSet ∧
      ConvexOn ℝ feasibleSet (fun x : (Fin p.n → ℝ) × (Fin p.n → ℝ) × ℝ => x.2.2) := by
  sorry

end «CAM-Bench-209»
