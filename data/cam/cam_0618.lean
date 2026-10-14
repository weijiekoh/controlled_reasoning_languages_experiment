import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-618»

open scoped BigOperators

theorem polynomial_isSOS_iff_exists_psd_gramMatrix
    {n k : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree = 2 * k) :
    (∃ r : ℕ, ∃ q : Fin r → MvPolynomial (Fin n) ℝ,
      (∀ i, (q i).totalDegree ≤ k) ∧
      p = ∑ i : Fin r, (q i) ^ 2) ↔
    ∃ (s : Type) (_ : Fintype s) (f : s → MvPolynomial (Fin n) ℝ),
      (∀ i : s, ∃ d : Fin n →₀ ℕ, d.sum (fun _ e => e) ≤ k ∧ f i = MvPolynomial.monomial d 1) ∧
      ∃ V : Matrix s s ℝ,
      V.IsSymm ∧
      (∀ z : s → ℝ, 0 ≤ dotProduct z (V.mulVec z)) ∧
      ∀ x : Fin n → ℝ,
        MvPolynomial.eval x p =
          dotProduct (fun i : s => MvPolynomial.eval x (f i))
            (V.mulVec (fun i : s => MvPolynomial.eval x (f i))) := by
  sorry

end «CAM-Bench-618»
