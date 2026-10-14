import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-263»

def convexConjugate (g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {t : EReal | ∃ x : Fin n → ℝ, g x ≠ ⊤ ∧ t = (∑ i, y i * x i) - g x}

open scoped BigOperators

theorem convexConjugate_lp_norm_power_eq
    {n : ℕ} {p q : ℝ}
    (h : ℝ → ℝ)
    (hp : 1 < p)
    (hh_def : h = fun t : ℝ => (1 / p : ℝ) * (max 0 t) ^ p)
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hh_monotone : Monotone h)
    (hh_nonpos : ∀ t : ℝ, t ≤ 0 → h t = h 0)
    (h_part_b :
      ∀ y : Fin n → ℝ,
        convexConjugate (fun x : Fin n → ℝ => (h ‖x‖ : EReal)) y =
          convexConjugate (fun t : Fin 1 → ℝ => (h (t 0) : EReal))
            (fun _ : Fin 1 => ‖y‖))
    (h_one_dim :
      ∀ s : ℝ,
        0 ≤ s →
        convexConjugate (fun t : Fin 1 → ℝ => (h (t 0) : EReal))
          (fun _ : Fin 1 => s) =
          (((1 / q : ℝ) * s ^ q : ℝ) : EReal))
    (hq : q = p / (p - 1))
    : ∀ y : Fin n → ℝ,
        convexConjugate
          (fun x : Fin n → ℝ => ((((1 / p : ℝ) * ‖x‖ ^ p : ℝ)) : EReal)) y =
          (((1 / q : ℝ) * ‖y‖ ^ q : ℝ) : EReal) := by
  sorry

end «CAM-Bench-263»
