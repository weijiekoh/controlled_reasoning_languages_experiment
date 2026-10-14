import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-156»

open Matrix

def IsLinearFractionalMap {n m : ℕ} (F : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ),
    ∀ x : Fin n → ℝ,
      (dotProduct c x + d > 0) →
        F x = fun i => ((A.mulVec x) i + b i) / (dotProduct c x + d)

theorem comp_linearFractional_isLinearFractional
    {n m p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d : ℝ)
    (E : Matrix (Fin p) (Fin m) ℝ)
    (f : Fin p → ℝ)
    (g : Fin m → ℝ)
    (h : ℝ) :
    let phi : (Fin n → ℝ) → (Fin m → ℝ) :=
      fun x i => ((A.mulVec x) i + b i) / (dotProduct c x + d)
    let Gamma : (Fin n → ℝ) → (Fin p → ℝ) :=
      fun x i =>
        ((E.mulVec (phi x)) i + f i) / (dotProduct g (phi x) + h)
    let AΓ : Matrix (Fin p) (Fin n) ℝ :=
      fun i j => ∑ k : Fin m, E i k * A k j + f i * c j
    let bΓ : Fin p → ℝ :=
      fun i => ∑ k : Fin m, E i k * b k + f i * d
    let cΓ : Fin n → ℝ :=
      fun j => ∑ k : Fin m, g k * A k j + h * c j
    let dΓ : ℝ := dotProduct g b + h * d
    ∀ x : Fin n → ℝ,
      dotProduct c x + d > 0 →
      dotProduct g (phi x) + h > 0 →
        Gamma x = fun i => ((AΓ.mulVec x) i + bΓ i) / (dotProduct cΓ x + dΓ) := by
  sorry

end «CAM-Bench-156»
