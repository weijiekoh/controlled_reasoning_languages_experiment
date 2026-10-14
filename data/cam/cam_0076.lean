import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-76»

def activeSet {ι : Type*} {X : Type*} (c : ι → X → ℝ) (x : X) : Set ι :=
  {i | c i x = 0}

def IsEqualityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => c x = 0

def IsInequalityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => 0 ≤ c x

def IsFeasiblePoint {ι : Type*} {X : Type*} (eqs ineqs : ι → X → ℝ) (x : X) : Prop :=
  (∀ i : ι, eqs i x = 0) ∧ (∀ i : ι, 0 ≤ ineqs i x)

open scoped BigOperators

theorem phi1_directionalDerivative_formula
    {n : ℕ} {ιE ιI : Type*}
    [Fintype ιE] [Fintype ιI]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (cE : ιE → EuclideanSpace ℝ (Fin n) → ℝ)
    (cI : ιI → EuclideanSpace ℝ (Fin n) → ℝ)
    (xhat p : EuclideanSpace ℝ (Fin n))
    [DecidablePred fun i : ιI => i ∈ activeSet cI xhat]
    (μ : ℝ)
    (hfd : DifferentiableAt ℝ f xhat)
    (hcE : ∀ i : ιE, DifferentiableAt ℝ (cE i) xhat)
    (hcI : ∀ i : ιI, DifferentiableAt ℝ (cI i) xhat)
    (hμ : 0 ≤ μ)
    (hEq : ∀ i : ιE, cE i xhat = 0)
    (hIneq : ∀ i : ιI, 0 ≤ cI i xhat) :
    Tendsto
      (fun α : ℝ =>
        ((f (xhat + α • p)
            + μ * (∑ i : ιE, |cE i (xhat + α • p)|)
            + μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p))))
          - (f xhat
            + μ * (∑ i : ιE, |cE i xhat|)
            + μ * (∑ i : ιI, max 0 (-cI i xhat)))) / α)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((fderiv ℝ f xhat) p
        + μ * (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|)
        + μ * (∑ i ∈ Finset.univ.filter (fun i : ιI => i ∈ activeSet cI xhat),
            max 0 (-(fderiv ℝ (cI i) xhat) p)))) := by
  sorry

end «CAM-Bench-76»
