import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-182»

def hicksianDemand (E : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ E p (Pi.single i 1)

def IsMarketClearing (S D : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) : Prop :=
  S p = D p

theorem unique_market_clearing_price_vector :
    let E : (Fin 4 → ℝ) → ℝ :=
      fun p => (7 / 10 : ℝ) * p 0 + (1 / 5 : ℝ) * p 1 +
        (1 / 10 : ℝ) * p 2 + (2 / 5 : ℝ) * p 3
    let S : (Fin 4 → ℝ) → (Fin 4 → ℝ) :=
      fun p =>
        ![(1 / 5 : ℝ) * p 0 + (1 / 2 : ℝ),
          (1 / 50 : ℝ) * p 1 + (1 / 10 : ℝ),
          (1 / 25 : ℝ) * p 2,
          (1 / 10 : ℝ) * p 3 + (1 / 5 : ℝ)]
    let pStar : Fin 4 → ℝ := ![1, 5, 5 / 2, 2]
    IsMarketClearing S (hicksianDemand E) pStar ∧
      hicksianDemand E pStar = ![(7 / 10 : ℝ), (1 / 5 : ℝ), (1 / 10 : ℝ), (2 / 5 : ℝ)] ∧
      S pStar = ![(7 / 10 : ℝ), (1 / 5 : ℝ), (1 / 10 : ℝ), (2 / 5 : ℝ)] ∧
      ∀ p : Fin 4 → ℝ, IsMarketClearing S (hicksianDemand E) p → p = pStar := by
  sorry

end «CAM-Bench-182»
