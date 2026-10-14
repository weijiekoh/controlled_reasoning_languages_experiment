import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-173»

def NPV {n : ℕ} (y : Fin (n + 1) → ℝ) (lam : {x : ℝ // 0 < x}) : ℝ :=
  ∑ j : Fin (n + 1), (lam : ℝ) ^ (j : ℕ) * y j

def IRR {n : ℕ} (y : Fin (n + 1) → ℝ) (r : ℝ) : Prop :=
  -1 < r ∧
    (∃ lam : {x : ℝ // 0 < x}, (lam : ℝ) = (1 + r)⁻¹ ∧ NPV y lam = 0) ∧
    ∀ r' : ℝ, -1 < r' →
      (∃ lam : {x : ℝ // 0 < x}, (lam : ℝ) = (1 + r')⁻¹ ∧ NPV y lam = 0) →
      r' = r

theorem IRR_weighted_average_le_max
    {n k : ℕ}
    (hk : 0 < k)
    (xv : Fin k → Fin (n + 1) → ℝ)
    (w : Fin k → ℝ)
    (hx0 : ∀ i : Fin k, xv i 0 < 0)
    (hxnonneg : ∀ i : Fin k, ∀ j : Fin (n + 1), j ≠ 0 → 0 ≤ xv i j)
    (hxsumpos : ∀ i : Fin k, 0 < ∑ j : Fin (n + 1), xv i j)
    (hwnonneg : ∀ i : Fin k, 0 ≤ w i)
    (hwsum : ∑ i : Fin k, w i = 1)
    (hirr_exists : ∀ i : Fin k, ∃ t : ℝ, IRR (xv i) t)
    (hirr_mono :
      ∀ y z : Fin (n + 1) → ℝ,
        y 0 < 0 →
        z 0 < 0 →
        (∀ j : Fin (n + 1), j ≠ 0 → 0 ≤ y j) →
        (∀ j : Fin (n + 1), j ≠ 0 → 0 ≤ z j) →
        0 < ∑ j : Fin (n + 1), y j →
        0 < ∑ j : Fin (n + 1), z j →
        (∀ j : Fin (n + 1), y j ≤ z j) →
        (∀ r₁ r₂ : ℝ, IRR y r₁ → IRR z r₂ → r₁ ≤ r₂)) :
    ∀ r : ℝ,
      IRR (fun j => ∑ i : Fin k, w i * xv i j) r →
      ∃ s : ℝ,
        IsGreatest {t : ℝ | ∃ i : Fin k, IRR (xv i) t} s ∧
        r ≤ s := by
  sorry

end «CAM-Bench-173»
