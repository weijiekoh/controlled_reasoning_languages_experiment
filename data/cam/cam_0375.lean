import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-375»

def IsSymmetricTridiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ ∀ i j : Fin n, 1 < Nat.dist i.1 j.1 → A i j = 0

theorem gradient_and_hessian_of_atv_objective
    {n : ℕ} (hn : 2 ≤ n) (xcor x : Fin n → ℝ) (ε μ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) :
    let i0 : Fin n := ⟨0, by omega⟩
    let inLast : Fin n := ⟨n - 1, by omega⟩
    let k0 : Fin (n - 1) := ⟨0, by omega⟩
    let kLast : Fin (n - 1) := ⟨n - 2, by omega⟩
    let d : Fin (n - 1) → ℝ := fun i =>
      x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩
    let w : Fin (n - 1) → ℝ := fun i =>
      ε ^ 2 / (Real.sqrt (ε ^ 2 + (d i) ^ 2)) ^ 3
    let ψ : (Fin n → ℝ) → ℝ := fun y =>
      (∑ i : Fin n, (y i - xcor i) ^ 2) +
        μ * (∑ i : Fin (n - 1),
          (Real.sqrt (ε ^ 2 + (y ⟨i.1 + 1, by omega⟩ - y ⟨i.1, by omega⟩) ^ 2) - ε))
    let e : Fin n → Fin n → ℝ := fun i j => if j = i then 1 else 0
    let hessEntry : Fin n → Fin n → ℝ := fun i j =>
      (fderiv ℝ (fun y => (fderiv ℝ ψ y) (e j)) x) (e i)
    ((fderiv ℝ ψ x) (e i0) =
        2 * (x i0 - xcor i0) -
          μ * d k0 / Real.sqrt (ε ^ 2 + (d k0) ^ 2)) ∧
      (∀ k : Fin (n - 2),
        let iMid : Fin n := ⟨k.1 + 1, by omega⟩
        let kLeft : Fin (n - 1) := ⟨k.1, by omega⟩
        let kRight : Fin (n - 1) := ⟨k.1 + 1, by omega⟩
        (fderiv ℝ ψ x) (e iMid) =
          2 * (x iMid - xcor iMid) +
            μ * (d kLeft / Real.sqrt (ε ^ 2 + (d kLeft) ^ 2) -
              d kRight / Real.sqrt (ε ^ 2 + (d kRight) ^ 2))) ∧
      ((fderiv ℝ ψ x) (e inLast) =
        2 * (x inLast - xcor inLast) +
          μ * d kLast / Real.sqrt (ε ^ 2 + (d kLast) ^ 2)) ∧
      (hessEntry i0 i0 = 2 + μ * w k0) ∧
      (∀ k : Fin (n - 2),
        let iMid : Fin n := ⟨k.1 + 1, by omega⟩
        let kLeft : Fin (n - 1) := ⟨k.1, by omega⟩
        let kRight : Fin (n - 1) := ⟨k.1 + 1, by omega⟩
        hessEntry iMid iMid = 2 + μ * (w kLeft + w kRight)) ∧
      (hessEntry inLast inLast = 2 + μ * w kLast) ∧
      (∀ i : Fin (n - 1),
        let iLeft : Fin n := ⟨i.1, by omega⟩
        let iRight : Fin n := ⟨i.1 + 1, by omega⟩
        hessEntry iLeft iRight = -μ * w i ∧
          hessEntry iRight iLeft = -μ * w i) ∧
      (∀ i j : Fin n, 1 < Nat.dist i.1 j.1 → hessEntry i j = 0) := by
  sorry

end «CAM-Bench-375»
