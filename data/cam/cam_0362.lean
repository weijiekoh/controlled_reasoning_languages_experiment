import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-362»

def bregmanDivergence {n : ℕ} (h : (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ) (_hh : DifferentiableAt ℝ h y) : ℝ :=
  h x - h y - ∑ i : Fin n, (fderiv ℝ h y) (Pi.single i (1 : ℝ)) * (x i - y i)

theorem bregmanDivergence_conj_eq_of_grad_conj_inverse
    {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (h_strictConvex : StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hf_diff : ∀ x : Fin n → ℝ, DifferentiableAt ℝ f x)
    (h_closed : IsClosed (Set.range f))
    (h_conj :
      ∀ u : Fin n → ℝ,
        g u = sSup ((fun x : Fin n → ℝ => (∑ i : Fin n, u i * x i) - f x) '' Set.univ))
    (h_grad_inv :
      Function.Bijective
        (fun x : Fin n → ℝ => fun i : Fin n => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) ∧
      ∀ u : Fin n → ℝ,
        (fun i : Fin n => (fderiv ℝ g u) (Pi.single i (1 : ℝ))) =
          Function.invFun
            (fun x : Fin n → ℝ => fun i : Fin n => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) u)
    (hg_diff :
      ∀ x : Fin n → ℝ,
        DifferentiableAt ℝ g
          (fun i : Fin n => (fderiv ℝ f x) (Pi.single i (1 : ℝ)))) :
    ∀ x y : Fin n → ℝ,
      bregmanDivergence g
        (fun i : Fin n => (fderiv ℝ f y) (Pi.single i (1 : ℝ)))
        (fun i : Fin n => (fderiv ℝ f x) (Pi.single i (1 : ℝ)))
        (hg_diff x) =
      bregmanDivergence f x y (hf_diff y) := by
  sorry

end «CAM-Bench-362»
