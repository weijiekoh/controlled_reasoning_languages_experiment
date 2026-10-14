import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-728»

open Matrix

def rayleighValues
    {n m : ℕ} (A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (z : Fin m → ℝ) :
    Set ℝ :=
  {μ : ℝ |
    ∃ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ = 1 ∧
        μ = dotProduct x (fun j => ((A 0 + ∑ i : Fin m, z i • A i.succ) *ᵥ x) j)}

theorem le_largestEigenvalue_iff_sub_posSemidef
    {n m : ℕ} [NeZero n]
    (A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, IsSymm (A i))
    (z : Fin m → ℝ) (η : ℝ)
    (hRayleigh_nonempty : (rayleighValues A z).Nonempty)
    (hRayleigh_bddAbove : BddAbove (rayleighValues A z)) :
    η ≥ sSup (rayleighValues A z) ↔
      PosSemidef (η • (1 : Matrix (Fin n) (Fin n) ℝ) - (A 0 + ∑ i : Fin m, z i • A i.succ)) := by
  sorry

end «CAM-Bench-728»
