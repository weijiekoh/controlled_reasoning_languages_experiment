import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-775»

def proper {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop := (∀ x, g x > ⊥) ∧ ∃ x, g x < ⊤

def lowerSemicontinuous {α : Type} [TopologicalSpace α] (g : α → EReal) : Prop :=
  ∀ x : α, ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) →
    g x ≤ Filter.liminf (fun k => g (u k)) atTop

def proximalOperator
    {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (g : α → EReal) (lam : ℝ) (y : α)
    (_hproper : (∀ x : α, g x > ⊥) ∧ ∃ x : α, g x < ⊤)
    (_hlsc : lowerSemicontinuous g)
    (_hconv : ConvexOn ℝ Set.univ (fun x : α => (g x).toReal))
    (_hlam : 0 < lam)
    (hmin :
      ∃ z : α, ∀ w : α,
        (lam : EReal) * g z + (((1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal) ≤
          (lam : EReal) * g w + (((1 / 2 : ℝ) * ‖w - y‖ ^ 2 : ℝ) : EReal)) :
    α :=
  Classical.choose hmin

theorem prox_h_eq_prox_theta_g
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (a : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hproper : proper g)
    (hlsc : lowerSemicontinuous g)
    (hconv : ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => (g x).toReal))
    (hproper_h :
      proper (fun x : Fin n → ℝ => g x + (((u / 2) * ‖x - a‖ ^ 2 : ℝ) : EReal)))
    (hlsc_h :
      lowerSemicontinuous
        (fun x : Fin n → ℝ => g x + (((u / 2) * ‖x - a‖ ^ 2 : ℝ) : EReal)))
    (hconv_h :
      ConvexOn ℝ Set.univ
        (fun x : Fin n → ℝ =>
          (g x + (((u / 2) * ‖x - a‖ ^ 2 : ℝ) : EReal)).toReal))
    (hmin_h : ∀ x : Fin n → ℝ,
      ∃ z : Fin n → ℝ, ∀ w : Fin n → ℝ,
        (1 : EReal) * (g z + (((u / 2) * ‖z - a‖ ^ 2 : ℝ) : EReal)) +
            (((1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal) ≤
          (1 : EReal) * (g w + (((u / 2) * ‖w - a‖ ^ 2 : ℝ) : EReal)) +
            (((1 / 2 : ℝ) * ‖w - x‖ ^ 2 : ℝ) : EReal))
    (hmin_g : ∀ x : Fin n → ℝ,
      ∃ z : Fin n → ℝ, ∀ w : Fin n → ℝ,
        ((1 / (1 + u) : ℝ) : EReal) * g z +
            (((1 / 2 : ℝ) *
              ‖z - ((1 / (1 + u) : ℝ) • x +
                (1 - (1 / (1 + u) : ℝ)) • a)‖ ^ 2 : ℝ) : EReal) ≤
          ((1 / (1 + u) : ℝ) : EReal) * g w +
            (((1 / 2 : ℝ) *
              ‖w - ((1 / (1 + u) : ℝ) • x +
                (1 - (1 / (1 + u) : ℝ)) • a)‖ ^ 2 : ℝ) : EReal)) :
    let h : (Fin n → ℝ) → EReal :=
      fun x => g x + (((u / 2) * ‖x - a‖ ^ 2 : ℝ) : EReal)
    let θ : ℝ := 1 / (1 + u)
    let hθpos : 0 < θ := by
      dsimp [θ]
      positivity
    ∀ x : Fin n → ℝ,
      proximalOperator h 1 x hproper_h hlsc_h hconv_h (by norm_num) (hmin_h x) =
        proximalOperator g θ (θ • x + (1 - θ) • a) hproper hlsc hconv hθpos (hmin_g x) := by
  sorry

end «CAM-Bench-775»
