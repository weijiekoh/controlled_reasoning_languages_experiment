import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-520»

theorem support_size_cover_quasiconcave_but_not_convex_concave_quasiconvex
    (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ℝ)
    (ha : StrictMono a) :
    let Δ : Set (Fin n → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1}
    let f : (Fin n → ℝ) → ℝ := by
      classical
      exact fun p =>
        let candidates : Finset (Finset (Fin n)) :=
          Finset.univ.powerset.filter
            (fun A : Finset (Fin n) => (0.9 : ℝ) ≤ Finset.sum A (fun i => p i))
        if hc : candidates.Nonempty then
          (((candidates.image (fun A : Finset (Fin n) => (A.image a).card)).min' (by
            simpa using hc.image (fun A : Finset (Fin n) => (A.image a).card)) : ℕ) : ℝ)
        else (n : ℝ)
    QuasiconcaveOn ℝ Δ f ∧
      ¬ ConvexOn ℝ Δ f ∧
      ¬ ConcaveOn ℝ Δ f ∧
      ¬ QuasiconvexOn ℝ Δ f := by
  sorry

end «CAM-Bench-520»
