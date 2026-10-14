import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-137»

def centralDifference (f : ℝ → ℝ) (ε : ℝ) (_hε : 0 < ε) : ℝ → ℝ :=
  fun x => (f (x + ε) - f (x - ε)) / (2 * ε)

def roundoffError (f f_tilde : ℝ → ℝ) (x : ℝ) : ℝ :=
  |f_tilde x - f x|

def IsOrderRoundoffError (f f_tilde : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ u0 : ℝ, 0 < u0 ∧ ∀ u : ℝ, 0 < u → u < u0 → roundoffError f f_tilde x ≤ C * u

def truncationError (Aε T : ℝ → ℝ) (x : ℝ) : ℝ :=
  Aε x - T x

theorem centralDifference_optimal_step_and_accuracy
    (f f_tilde : ℝ → ℝ) (x : ℝ)
    (hround :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ u0 : ℝ, 0 < u0 ∧ ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ u : ℝ, 0 < u → u < u0 →
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            |f_tilde (x + ε) - f (x + ε)| ≤ C * u ∧
            |f_tilde (x - ε) - f (x - ε)| ≤ C * u)
    (htrunc :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ ε : ℝ, ∀ hε : 0 < ε, ε < ε0 →
          |truncationError (fun y => centralDifference f ε hε y) (fun y => deriv f y) x| ≤ C * ε^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ u0 : ℝ, 0 < u0 ∧
      ∀ u : ℝ, ∀ hu : 0 < u, u < u0 →
        let ε := u ^ (1 / (3 : ℝ))
        |centralDifference f_tilde ε (by
            have hε : 0 < ε := by
              dsimp [ε]
              exact Real.rpow_pos_of_pos hu (1 / (3 : ℝ))
            exact hε) x - deriv f x| ≤ C * u ^ (2 / (3 : ℝ)) := by
  sorry

end «CAM-Bench-137»
