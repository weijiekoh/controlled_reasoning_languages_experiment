import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-81»

def consistent {α : Type*} (constraints : Set α) : Prop :=
  ∃ x, x ∈ constraints

def vacuous {α ι : Type*} [IsEmpty ι] (constraints : ι → Set α) : Prop :=
  ∀ x : α, ∀ i : ι, x ∈ constraints i

theorem linearized_constraint_system_consistent
    {n : ℕ} {Ε Ι : Type*} [Fintype Ε] [Fintype Ι]
    (xk : Fin n → ℝ)
    (c : Sum Ε Ι → (Fin n → ℝ) → ℝ)
    (g : Sum Ε Ι → Fin n → ℝ)
    (hc_diff : ∀ i : Sum Ε Ι, DifferentiableAt ℝ (c i) xk)
    (hgrad : ∀ i : Sum Ε Ι,
      g i = fun j => (fderiv ℝ (c i) xk) (Pi.single j (1 : ℝ)))
    (Δk : ℝ)
    (hΔk : 0 ≤ Δk) :
    consistent
      {z :
          (Fin n → ℝ) × (Ε → ℝ) × (Ε → ℝ) × (Ι → ℝ) |
        let p := z.1
        let v := z.2.1
        let w := z.2.2.1
        let t := z.2.2.2
        (∀ i : Ε, (∑ j : Fin n, g (.inl i) j * p j) + c (.inl i) xk = v i - w i) ∧
        (∀ i : Ι, -(t i) ≤ (∑ j : Fin n, g (.inr i) j * p j) + c (.inr i) xk) ∧
        (∀ i : Ε, 0 ≤ v i) ∧
        (∀ i : Ε, 0 ≤ w i) ∧
        (∀ i : Ι, 0 ≤ t i) ∧
        (∀ j : Fin n, |p j| ≤ Δk)} := by
  sorry

end «CAM-Bench-81»
