import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-774»

open scoped BigOperators

noncomputable def prox_f {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Fin n → ℝ :=
  sInf {u | IsMinOn
    (fun v : Fin n → ℝ => f v + ((1 : EReal) / 2) * ((ENNReal.ofReal ‖v - x‖ : EReal) ^ (2 : ℕ)))
    Set.univ u}

theorem prox_add_linear_eq_prox_shift {n : ℕ} (g : (Fin n → ℝ) → EReal) (a x : Fin n → ℝ)
    (hprox_well_defined :
      ∀ y : Fin n → ℝ,
        ∃! u : Fin n → ℝ,
          IsMinOn
            (fun v : Fin n → ℝ =>
              (g v + (((∑ i : Fin n, a i * v i) : ℝ) : EReal)) +
                ((1 : EReal) / 2) * ((ENNReal.ofReal ‖v - y‖ : EReal) ^ (2 : ℕ)))
            Set.univ u)
    (gprox_well_defined :
      ∀ y : Fin n → ℝ,
        ∃! u : Fin n → ℝ,
          IsMinOn
            (fun v : Fin n → ℝ =>
              g v + ((1 : EReal) / 2) * ((ENNReal.ofReal ‖v - y‖ : EReal) ^ (2 : ℕ)))
            Set.univ u) :
    prox_f (fun u => g u + (((∑ i : Fin n, a i * u i) : ℝ) : EReal)) x = prox_f g (x - a) := by
  sorry

end «CAM-Bench-774»
