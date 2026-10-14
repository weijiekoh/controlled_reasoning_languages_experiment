import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-414»

abbrev ConeProper {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (∀ ⦃x y : Fin n → ℝ⦄, x ∈ K → y ∈ K → x + y ∈ K) ∧
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  (K ∩ Neg.neg '' K = ({0} : Set (Fin n → ℝ))) ∧
  (interior K).Nonempty

abbrev ConeSolid {n : ℕ} (K : ProperCone ℝ (Fin n → ℝ)) : Prop :=
  ConeProper (K : Set (Fin n → ℝ))

theorem gradient_eq_neg_hessian_mul_self_of_log_homogeneous
    {n : ℕ}
    (K : ProperCone ℝ (Fin n → ℝ))
    (hK : ConeSolid K)
    (ψext : (Fin n → ℝ) → ℝ)
    (θ : ℝ)
    (hψ_smooth :
      ContDiffOn ℝ 2 ψext (interior (K : Set (Fin n → ℝ))))
    (hscale :
      ∀ (y : interior (K : Set (Fin n → ℝ))) (t : ℝ), 0 < t →
        t • (y : Fin n → ℝ) ∈ interior (K : Set (Fin n → ℝ)))
    (hψ :
      ∀ (y : interior (K : Set (Fin n → ℝ))),
        ∀ (t : ℝ), 0 < t →
          ψext (t • (y : Fin n → ℝ)) = ψext y - θ * Real.log t) :
    ∀ y : interior (K : Set (Fin n → ℝ)),
      ∀ i : Fin n,
        (fderivWithin ℝ
            ψext
            (interior (K : Set (Fin n → ℝ))) (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))
        =
        -(∑ j : Fin n,
            ((fderivWithin ℝ
                (fun z : Fin n → ℝ =>
                  (fderivWithin ℝ
                    ψext
                    (interior (K : Set (Fin n → ℝ))) z) (Pi.single j (1 : ℝ)))
                (interior (K : Set (Fin n → ℝ))) (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))) * y.1 j) := by
  sorry

end «CAM-Bench-414»
