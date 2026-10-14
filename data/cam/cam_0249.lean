import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-249»

def schurComplement
    {m n : Type*}
    [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ)
    (B : Matrix m n ℝ)
    (C : Matrix n n ℝ)
    (_hC : IsUnit C.det) : Matrix m m ℝ :=
  let _inst : Invertible C := Matrix.invertibleOfIsUnitDet C _hC
  A - B * (⅟ C) * B.transpose

theorem schurComplement_inv_eq_compression_of_block
    {m k : Type*}
    [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k]
    (X : Matrix (m ⊕ k) (m ⊕ k) ℝ)
    (P : Matrix (m ⊕ k) m ℝ)
    (X₁₁ : Matrix m m ℝ)
    (X₁₂ : Matrix m k ℝ)
    (X₂₂ : Matrix k k ℝ)
    (hP_rank : Module.finrank ℝ ((Matrix.toLin' P).range) = Fintype.card m)
    (hX : X = Matrix.fromBlocks X₁₁ X₁₂ X₁₂.transpose X₂₂)
    (hP : P = fun i j =>
      match i with
      | Sum.inl i' => (1 : Matrix m m ℝ) i' j
      | Sum.inr _ => 0)
    (hXpos : X.PosDef)
    (hX₂₂_inv : IsUnit X₂₂.det) :
    (schurComplement X₁₁ X₁₂ X₂₂ hX₂₂_inv)⁻¹ = P.transpose * X⁻¹ * P := by
  sorry

end «CAM-Bench-249»
