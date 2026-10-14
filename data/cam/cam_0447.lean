import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-447»

def IsLinearFractional {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [Module.Free ℝ α] [Module.Finite ℝ α]
    [AddCommGroup β] [Module ℝ β] [Module.Free ℝ β] [Module.Finite ℝ β]
    (f : α → β) : Prop :=
  let domBasis : Module.Basis (Fin (Module.finrank ℝ α)) ℝ α := Module.finBasis ℝ α
  let codBasis : Module.Basis (Fin (Module.finrank ℝ β)) ℝ β := Module.finBasis ℝ β
  ∃ A : Matrix (Fin (Module.finrank ℝ β)) (Fin (Module.finrank ℝ α)) ℝ,
    ∃ b : Fin (Module.finrank ℝ β) → ℝ,
      ∃ c : Fin (Module.finrank ℝ α) → ℝ,
        ∃ d : ℝ,
            ∀ x,
              0 < dotProduct c (domBasis.equivFun x) + d →
              f x =
                codBasis.equivFun.symm
                  (fun i =>
                    (A.mulVec (domBasis.equivFun x) i + b i) /
                      (dotProduct c (domBasis.equivFun x) + d))

theorem preimage_linear_matrix_inequality_eq
    {m n p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ)
    (c : Fin m → ℝ)
    (d : ℝ)
    (Ams : Fin n → Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    let f : (Fin m → ℝ) → (Fin n → ℝ) :=
      fun x i => (A.mulVec x i + b i) / (dotProduct c x + d)
    let C : Set (Fin n → ℝ) :=
      {y | Matrix.PosSemidef (B - (∑ i : Fin n, y i • Ams i))}
    let G : Fin m → Matrix (Fin p) (Fin p) ℝ :=
      fun j => (∑ i : Fin n, (A i j) • Ams i) - (c j) • B
    let H : Matrix (Fin p) (Fin p) ℝ :=
      d • B - (∑ i : Fin n, (b i) • Ams i)
    {x : Fin m → ℝ | 0 < dotProduct c x + d ∧ f x ∈ C} =
      {x : Fin m → ℝ | 0 < dotProduct c x + d ∧ Matrix.PosSemidef (H - (∑ j : Fin m, (x j) • G j))} := by
  sorry

end «CAM-Bench-447»
