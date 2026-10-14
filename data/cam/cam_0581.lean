import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-581»

def Hessian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

open scoped Matrix

theorem convex_on_affine_set_iff_hessian_shifted_psd
    {n m p : ℕ}
    (F : Matrix (Fin n) (Fin m) ℝ)
    (xHat : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ)
    (dom : Set (Fin n → ℝ))
    (hconv_dom : Convex ℝ dom)
    (hopen_dom : IsOpen dom)
    (hAF : A * F = 0)
    (hrank : Matrix.rank A = n - Matrix.rank F)
    (hC2 : ∀ z : Fin m → ℝ,
      (fun i => ∑ j, F i j * z j + xHat i) ∈ dom →
      ContDiffAt ℝ 2 f (fun i => ∑ j, F i j * z j + xHat i))
    :
    ConvexOn ℝ {x | x ∈ dom ∧ ∃ z : Fin m → ℝ, x = fun i => ∑ j, F i j * z j + xHat i} f ↔
      ∀ z ∈ {z : Fin m → ℝ | (fun i => ∑ j, F i j * z j + xHat i) ∈ dom},
        (Hessian f (fun i => ∑ j, F i j * z j + xHat i)).IsSymm ∧
        ∃ lam : ℝ,
          ∀ v : Fin n → ℝ,
            0 ≤
              dotProduct v
                ((((Hessian f (fun i => ∑ j, F i j * z j + xHat i)) +
                  lam • (A.transpose * A)).mulVec v)) := by
  sorry

end «CAM-Bench-581»
