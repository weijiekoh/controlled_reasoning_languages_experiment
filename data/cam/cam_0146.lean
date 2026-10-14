import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-146»

def forwardFiniteDifferenceApproxGradient (f : (Fin n → ℝ) → ℝ) (ε : ℝ)
    (x : Fin n → ℝ) (_hε : 0 < ε) : Fin n → ℝ :=
  fun i => (f (x + fun j => if j = i then ε else 0) - f x) / ε

open scoped BigOperators

theorem norm_forwardFiniteDifferenceApproxGradient_sub_gradient_le
    {n : ℕ}
    (f h φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (ε Lh : ℝ)
    (hf : f = fun y => h y + φ y)
    (hn : 0 < n)
    (hε : 0 < ε)
    (grad_h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hneigh :
      ∃ U : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧
        {z : EuclideanSpace ℝ (Fin n) |
            (∀ i, x i ≤ z i) ∧
            sSup (Set.range fun i : Fin n => |(z - x) i|) ≤ ε} ⊆ U ∧
        (∀ z : EuclideanSpace ℝ (Fin n), z ∈ U → HasGradientAt h (grad_h z) z) ∧
        (∀ u v : EuclideanSpace ℝ (Fin n), u ∈ U → v ∈ U →
          sSup (Set.range fun i : Fin n => |(grad_h u - grad_h v) i|) ≤
            Lh * sSup (Set.range fun i : Fin n => |(u - v) i|)))
    (η : ℝ)
    (hη_nonneg : 0 ≤ η)
    (hη_bound :
      ∀ z : EuclideanSpace ℝ (Fin n),
        (∀ i, x i ≤ z i) →
        sSup (Set.range fun i : Fin n => |(z - x) i|) ≤ ε →
        |φ z| ≤ η) :
    let toFun : EuclideanSpace ℝ (Fin n) → Fin n → ℝ :=
      EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let fromFun : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm
    let supNorm : (Fin n → ℝ) → ℝ :=
      fun v => sSup (Set.range fun i : Fin n => |v i|)
    supNorm
        (forwardFiniteDifferenceApproxGradient
            (fun y => f (fromFun y)) ε (toFun x) hε -
          toFun (grad_h x)) ≤
      Lh * ε + η / ε := by
  sorry

end «CAM-Bench-146»
