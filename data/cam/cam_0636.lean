import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-636»

def effectiveDomain {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x < ⊤}

def epigraph {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set ((Fin n → ℝ) × EReal) :=
  {p | f p.1 ≤ p.2}

def IsClosedFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (effectiveDomain f).Nonempty ∧ IsClosed (epigraph f)

def fenchelConjugate {m : ℕ} (p : (Fin m → ℝ) → EReal) : (Fin m → ℝ) → EReal :=
  fun v => sSup {a | ∃ u : Fin m → ℝ, a = (∑ i, u i * v i : ℝ) - p u}

theorem fenchelConjugate_p_eq_inf_indicator_neg
    {n m : ℕ}
    (W : Set (Fin n → ℝ))
    (Z : Set (Fin m → ℝ))
    [DecidablePred fun w => w ∈ W]
    [DecidablePred fun z => z ∈ Z]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hW : W.Nonempty)
    (hZ : Z.Nonempty)
    (hdom : ∀ w ∈ W, ∀ z ∈ Z, ((f w z : ℝ) : EReal) < ⊤)
    (hg_closed_convex :
      ∀ z ∈ Z,
        IsClosedFunction
          (fun w => if w ∈ W then (f w z : EReal) else ⊤) ∧
        Convex ℝ
          {p : (Fin n → ℝ) × ℝ |
            (if p.1 ∈ W then (f p.1 z : EReal) else ⊤) ≤ (p.2 : EReal)})
    (hh_closed_convex :
      ∀ w ∈ W,
        IsClosedFunction
          (fun z => if z ∈ Z then ((-f w z : ℝ) : EReal) else ⊤) ∧
        Convex ℝ
          {p : (Fin m → ℝ) × ℝ |
            (if p.1 ∈ Z then ((-f w p.1 : ℝ) : EReal) else ⊤) ≤ (p.2 : EReal)})
    (p : (Fin m → ℝ) → EReal)
    (hp :
      p =
        fun u =>
          sInf
            ((fun w : Fin n → ℝ =>
              sSup ((fun z : Fin m → ℝ => ((f w z + ∑ i, u i * z i : ℝ) : EReal)) '' Z)) '' W)) :
    fenchelConjugate p =
      fun v =>
        if v ∈ Z then
          -sInf ((fun w : Fin n → ℝ => ((f w v : ℝ) : EReal)) '' W)
        else
          ⊤ := by
  sorry

end «CAM-Bench-636»
