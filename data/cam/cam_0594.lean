import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-594»

def Quasiconvex (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ D ∧ ∀ α : ℝ, Convex ℝ {x | x ∈ D ∧ f x ≤ α}

def sublevelSet (D : Set ℝ) (f : ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {x | x ∈ D ∧ f x ≤ α}

open scoped BigOperators

theorem linf_ball_fractional_l1_objective_quasiconvex
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hd : d > ∑ i, |c i|) :
    let C : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ (1 : ℝ)}
    let f : (Fin n → ℝ) → ℝ := fun x => (∑ i, |(A.mulVec x - b) i|) / ((∑ i, c i * x i) + d)
    (∀ x ∈ C, (∑ i, c i * x i) + d > 0) ∧
      QuasiconvexOn ℝ C f := by
  sorry

end «CAM-Bench-594»
