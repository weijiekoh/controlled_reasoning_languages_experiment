import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-199»

theorem feasibleSet_convex_and_minimum_time_by_smallest_horizon
    (m g h α Fmax : ℝ)
    (hm : 0 < m)
    (hg : 0 < g)
    (hh : 0 < h)
    (hα : 0 < α)
    (hFmax : 0 < Fmax)
    (p1 v1 : Fin 3 → ℝ) :
    let e3 : Fin 3 → ℝ := fun i => if i = 2 then 1 else 0;
    let StateSeq : ℕ → Type := fun K => (Fin (K + 1) → Fin 3 → ℝ) ×
      (Fin (K + 1) → Fin 3 → ℝ) × (Fin K → Fin 3 → ℝ);
    let feasible : (K : ℕ) → Set (StateSeq K) :=
      fun K =>
        {x : StateSeq K |
          let p := x.1
          let v := x.2.1
          let f := x.2.2
          v 0 = v1 ∧
          p 0 = p1 ∧
          (∀ k : Fin K,
            v k.succ = v k.castSucc + (h / m) • f k - (h * g) • e3) ∧
          (∀ k : Fin K,
            p k.succ = p k.castSucc + (h / 2) • (v k.castSucc + v k.succ)) ∧
          p (Fin.last K) = 0 ∧
          v (Fin.last K) = 0 ∧
          (∀ k : Fin (K + 1),
            α * Real.sqrt ((p k 0) ^ 2 + (p k 1) ^ 2) ≤ p k 2) ∧
          (∀ k : Fin K, ‖f k‖ ≤ Fmax)};
    (∀ K : ℕ, 1 ≤ K → Convex ℝ (feasible K)) ∧
      ((∃ K : ℕ, 1 ≤ K ∧ (feasible K).Nonempty) →
        ∃ Kmin : ℕ,
          1 ≤ Kmin ∧
          (feasible Kmin).Nonempty ∧
          (∀ K : ℕ, 1 ≤ K → (feasible K).Nonempty → Kmin ≤ K)) := by
  sorry

end «CAM-Bench-199»
