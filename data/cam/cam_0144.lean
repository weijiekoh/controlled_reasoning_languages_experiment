import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-144»

open scoped RealInnerProductSpace

theorem kappa_Dk_ge_one_div_sqrt_add_two
    (n : ℕ) (hn : 1 ≤ n) :
    let e : EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm (fun _ => (1 : ℝ))
    let Dk : Fin (n + 1) → EuclideanSpace ℝ (Fin n)
      | ⟨i, hi⟩ =>
          if h : i < n then
            ((1 : ℝ) / (2 * n : ℝ)) • e - EuclideanSpace.single ⟨i, h⟩ (1 : ℝ)
          else
            ((1 : ℝ) / (2 * n : ℝ)) • e
    0 < (1 / Real.sqrt (4 * n + 1) : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n),
        v ≠ 0 →
          (1 / Real.sqrt (4 * n + 1) : ℝ) ≤
            Finset.univ.sup'
              Finset.univ_nonempty
              (fun i : Fin (n + 1) =>
                ⟪v, Dk i⟫ / (‖v‖ * ‖Dk i‖)) := by
  sorry

end «CAM-Bench-144»
