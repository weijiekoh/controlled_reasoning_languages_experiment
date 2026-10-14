import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-694»

def IsEuclideanProjection {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) (z p : EuclideanSpace ℝ (Fin m)) :
    Prop :=
  p ∈ C ∧ ∀ y ∈ C, ‖p - z‖ ≤ ‖y - z‖

theorem secondOrderCone_projection_formula
    {n : ℕ}
    (x0 : EuclideanSpace ℝ (Fin n))
    (t0 : ℝ) :
    ∃! p : EuclideanSpace ℝ (Fin n.succ),
      IsEuclideanProjection
        {q : EuclideanSpace ℝ (Fin n.succ) |
          ‖(EuclideanSpace.equiv (Fin n) ℝ).symm
              (fun i : Fin n => (EuclideanSpace.equiv (Fin n.succ) ℝ q) (Fin.castSucc i))‖ ≤
            (EuclideanSpace.equiv (Fin n.succ) ℝ q) (Fin.last n)}
        ((EuclideanSpace.equiv (Fin n.succ) ℝ).symm
          (fun i : Fin n.succ =>
            if h : i.1 < n then
              (EuclideanSpace.equiv (Fin n) ℝ x0) ⟨i.1, h⟩
            else
              t0))
        p ∧
      p =
        (if h1 : ‖x0‖ ≤ -t0 then
          0
        else if h2 : ‖x0‖ ≤ t0 then
          (EuclideanSpace.equiv (Fin n.succ) ℝ).symm
            (fun i : Fin n.succ =>
              if h : i.1 < n then
                (EuclideanSpace.equiv (Fin n) ℝ x0) ⟨i.1, h⟩
              else
                t0)
        else
          (EuclideanSpace.equiv (Fin n.succ) ℝ).symm
            (fun i : Fin n.succ =>
              let alpha : ℝ := (1 / 2 : ℝ) * (1 + t0 / ‖x0‖)
              if h : i.1 < n then
                alpha * (EuclideanSpace.equiv (Fin n) ℝ x0) ⟨i.1, h⟩
              else
                alpha * ‖x0‖)) := by
  sorry

end «CAM-Bench-694»
