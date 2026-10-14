import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-380»

def logLikelihood (p : α → β → ℝ) (z : β) : α → ℝ :=
  fun x => Real.log (p x z)

def maximumLikelihoodEstimators (p : α → β → ℝ) (z : β) : Set α :=
  {x | ∀ y, logLikelihood p z y ≤ logLikelihood p z x}

theorem maximumLikelihoodEstimation_is_convex_optimization
    {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (ybar : Fin m → ℤ)
    (hybar : ∀ i, ybar i = 1 ∨ ybar i = -1) :
    let p : (Fin n → ℝ) → (Fin m → ℤ) → ℝ :=
      fun x y =>
        Real.exp
          (∑ i : Fin m,
            if y i = 1 then
              Real.log
                (((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                  (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                    Real.exp (-(t ^ 2) / 2)))
            else
              Real.log
                (1 -
                  (((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                    (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                      Real.exp (-(t ^ 2) / 2)))))
    let l : (Fin n → ℝ) → ℝ := logLikelihood p ybar
    ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) l ∧
      Convex ℝ (maximumLikelihoodEstimators p ybar) := by
  sorry

end «CAM-Bench-380»
