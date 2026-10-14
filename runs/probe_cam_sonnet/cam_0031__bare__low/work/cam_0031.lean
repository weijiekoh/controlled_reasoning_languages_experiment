import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-31»

theorem last_row_factorization_coefficients
    (ν11 u13 u14 u15 w1 u33 u34 u35 w3 u44 u45 w4 u55 w5 hatw2 u23 u24 u25 w2 l52 l53 l54 : ℝ)
    (hu33 : u33 ≠ 0) (hu44 : u44 ≠ 0) (hu55 : u55 ≠ 0)
    (hrow :
      (![0, l52 * u33, l52 * u34 + l53 * u44, l52 * u35 + l53 * u45 + l54 * u55,
          l52 * w3 + l53 * w4 + l54 * w5 + hatw2] : Fin 5 → ℝ) =
      ![0, u23, u24, u25, w2]) :
    l52 = u23 / u33 ∧
    l53 = (u24 - l52 * u34) / u44 ∧
    l54 = (u25 - l52 * u35 - l53 * u45) / u55 ∧
    hatw2 = w2 - l52 * w3 - l53 * w4 - l54 * w5 := by
  have h1 := congrFun hrow 1
  have h2 := congrFun hrow 2
  have h3 := congrFun hrow 3
  have h4 := congrFun hrow 4
  simp at h1 h2 h3 h4
  have e1 : l52 = u23 / u33 := by field_simp; linarith
  have e2 : l53 = (u24 - l52 * u34) / u44 := by field_simp; linarith
  have e3 : l54 = (u25 - l52 * u35 - l53 * u45) / u55 := by field_simp; linarith
  exact ⟨e1, e2, e3, by linarith⟩

end «CAM-Bench-31»
