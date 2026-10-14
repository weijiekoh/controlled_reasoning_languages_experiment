import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-313»

def infimalConvolution {n : ℕ} (m : ℕ) (f : Fin m → (EuclideanSpace ℝ (Fin n) → EReal)) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun x =>
    sInf
      {t : EReal |
        ∃ xs : Fin m → EuclideanSpace ℝ (Fin n),
          (∑ i, xs i = x) ∧ (∑ i, f i (xs i) = t)}

def convexConjugate (h : EuclideanSpace ℝ (Fin m) → EReal) :
    EuclideanSpace ℝ (Fin m) → EReal :=
  fun y =>
    sSup {t : EReal | ∃ x : EuclideanSpace ℝ (Fin m), t = (∑ i, (y i) * (x i)) - h x}

def IsConvexERealFn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ConvexOn ℝ Set.univ (fun x => EReal.toReal (f x)) ∧
    ∃ x : EuclideanSpace ℝ (Fin n), f x ≠ ⊤

theorem convexConjugate_infimalConvolution_eq_sum_convexConjugate
    (n m : ℕ)
    (hm : 0 < m)
    (f : Fin m → (EuclideanSpace ℝ (Fin n) → EReal))
    (hf_convex : ∀ i : Fin m, IsConvexERealFn (f i))
    (hf_proper : ∀ i : Fin m, ∃ x : EuclideanSpace ℝ (Fin n), f i x ≠ ⊤) :
    @convexConjugate n (infimalConvolution m f)
      =
    fun y => ∑ i, @convexConjugate n (f i) y := by
  sorry

end «CAM-Bench-313»
