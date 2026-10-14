import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-519»

def Quasiconvex (C : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ C ∧
    ∀ ⦃x y : ℝ⦄, x ∈ C → y ∈ C → ∀ ⦃lam : ℝ⦄, lam ∈ Set.Icc (0 : ℝ) 1 →
      f (lam * x + (1 - lam) * y) ≤ max (f x) (f y)

def Quasiconcave (C : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ C ∧
    ∀ ⦃x y : ℝ⦄, x ∈ C → y ∈ C → ∀ ⦃lam : ℝ⦄, lam ∈ Set.Icc (0 : ℝ) 1 →
      f (lam * x + (1 - lam) * y) ≥ min (f x) (f y)

theorem quartile_on_simplex_quasiconvex_quasiconcave_not_convex_not_concave
    {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℝ)
    (ha : StrictMono a) :
    let Δ : Set (Fin n → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1)}
    let q : (Fin n → ℝ) → ℝ := fun p =>
      sInf {β : ℝ | (0.25 : ℝ) ≤ ∑ i : Fin n, if a i ≤ β then p i else 0}
    QuasiconvexOn ℝ Δ q ∧
      QuasiconcaveOn ℝ Δ q ∧
      ¬ ConvexOn ℝ Δ q ∧
      ¬ ConcaveOn ℝ Δ q := by
  sorry

end «CAM-Bench-519»
