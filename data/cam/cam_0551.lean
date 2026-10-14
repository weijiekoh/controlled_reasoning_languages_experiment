import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-551»

def IsConvexC2Function {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) : Prop :=
  ConvexOn ℝ (Set.univ : Set E) f ∧ ContDiff ℝ 2 f

def convexConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) : E → EReal :=
  fun y => sSup (Set.range fun z : E => (⟪y, z⟫ : ℝ) - f z)

def IsDifferentiableAtWithGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → ℝ) (y a : E) : Prop :=
  HasFDerivAt g ((InnerProductSpace.toDual ℝ E) a) y

theorem gradient_convexConjugate_at_gradient_eq_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ)
    (x : E)
    (hf : IsConvexC2Function f)
    (hpd : ∀ v : E, v ≠ 0 →
      0 < (fderiv ℝ (fun z : E => fderiv ℝ f z v) x) v)
    (y : E)
    (hy : y = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) :
    ∃ g : E → ℝ,
      (∀ y' : E, convexConjugate (fun z : E => (f z : EReal)) y' = (g y' : EReal)) ∧
      IsDifferentiableAtWithGradient g y x := by
  sorry

end «CAM-Bench-551»
