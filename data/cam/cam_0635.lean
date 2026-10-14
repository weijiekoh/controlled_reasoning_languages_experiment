import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-635»

def effectiveDomain {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x < ⊤}

def epigraph {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set ((Fin n → ℝ) × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

def IsClosedFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsClosed (epigraph f)

open scoped RealInnerProductSpace
theorem p_isConvex
    {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (W : Set (Fin n → ℝ))
    (Z : Set (Fin m → ℝ))
    [DecidablePred fun w => w ∈ W]
    [DecidablePred fun z => z ∈ Z]
    (hW : W.Nonempty)
    (hZ : Z.Nonempty)
    (hdom :
      Set.prod W Z ⊆
        {p : (Fin n → ℝ) × (Fin m → ℝ) | ((f p.1 p.2 : EReal) < ⊤)})
    (gz :
      ∀ z, z ∈ Z →
        IsClosedFunction (fun w : Fin n → ℝ => if h : w ∈ W then (f w z : EReal) else ⊤))
    (gz_convex :
      ∀ z, z ∈ Z →
        Convex ℝ
          {p : (Fin n → ℝ) × ℝ |
            p.1 ∈ effectiveDomain (fun w : Fin n → ℝ => if h : w ∈ W then (f w z : EReal) else ⊤) ∧
            (fun w : Fin n → ℝ => if h : w ∈ W then (f w z : EReal) else ⊤) p.1 ≤ (p.2 : EReal)})
    (hw :
      ∀ w, w ∈ W →
        IsClosedFunction (fun z : Fin m → ℝ => if h : z ∈ Z then ((-f w z : ℝ) : EReal) else ⊤))
    (hw_convex :
      ∀ w, w ∈ W →
        Convex ℝ
          {p : (Fin m → ℝ) × ℝ |
            p.1 ∈ effectiveDomain (fun z : Fin m → ℝ => if h : z ∈ Z then ((-f w z : ℝ) : EReal) else ⊤) ∧
            (fun z : Fin m → ℝ => if h : z ∈ Z then ((-f w z : ℝ) : EReal) else ⊤) p.1 ≤ (p.2 : EReal)}) :
    let p : (Fin m → ℝ) → EReal := fun u : Fin m → ℝ =>
      sInf ((fun w : Fin n → ℝ =>
        sSup ((fun z : Fin m → ℝ =>
          ((f w z + dotProduct u z : ℝ) : EReal)) '' Z)) '' W)
    Convex ℝ (epigraph p) := by
  sorry

end «CAM-Bench-635»
