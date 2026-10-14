import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-637»

theorem partial_infimum_isClosed_of_bounded_sublevelSets
    {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (W : Set (Fin n → ℝ))
    (Z : Set (Fin m → ℝ))
    [DecidablePred (fun w : Fin n → ℝ => w ∈ W)]
    [DecidablePred (fun z : Fin m → ℝ => z ∈ Z)]
    (hW : W.Nonempty)
    (hZ : Z.Nonempty)
    (hg_closed_convex :
      ∀ z ∈ Z,
        IsClosed
          {p : (Fin n → ℝ) × ℝ |
            (if p.1 ∈ W then (((f p.1 z : ℝ) : WithTop ℝ)) else ⊤) ≤ (p.2 : WithTop ℝ)} ∧
          Convex ℝ
            {p : (Fin n → ℝ) × ℝ |
              (if p.1 ∈ W then (((f p.1 z : ℝ) : WithTop ℝ)) else ⊤) ≤ (p.2 : WithTop ℝ)})
    (hh_closed_convex :
      ∀ w ∈ W,
        IsClosed
          {p : (Fin m → ℝ) × ℝ |
            (if p.1 ∈ Z then (((-f w p.1 : ℝ) : WithTop ℝ)) else ⊤) ≤ (p.2 : WithTop ℝ)} ∧
          Convex ℝ
            {p : (Fin m → ℝ) × ℝ |
              (if p.1 ∈ Z then (((-f w p.1 : ℝ) : WithTop ℝ)) else ⊤) ≤ (p.2 : WithTop ℝ)})
    (hg_bounded :
      ∀ z ∈ Z,
        ∀ α : ℝ,
          Bornology.IsBounded
            {w : Fin n → ℝ |
              (if w ∈ W then (((f w z : ℝ) : WithTop ℝ)) else ⊤) ≤ (α : WithTop ℝ)}) :
    IsClosed
      {q : (Fin m → ℝ) × ℝ |
        (if q.1 ∈ Z then
          sInf ((fun w : Fin n → ℝ => (((f w q.1 : ℝ) : WithTop ℝ))) '' W)
        else ⊤) ≤ (q.2 : WithTop ℝ)} := by
  sorry

end «CAM-Bench-637»
