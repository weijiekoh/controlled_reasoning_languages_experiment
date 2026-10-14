import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-122»

def IsExactLineSearch {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) (x p : E) (αk : ℝ) : Prop :=
  ∀ α : ℝ, f (x + αk • p) ≤ f (x + α • p)

open scoped BigOperators

def IsQuadraticFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ Q : Matrix (Fin n) (Fin n) ℝ,
    Q.IsSymm ∧ ∃ q : Fin n → ℝ, ∃ r : ℝ,
      ∀ x : Fin n → ℝ,
        f x =
          (1 / 2 : ℝ) * ∑ i : Fin n, x i * ∑ j : Fin n, Q i j * x j
            + ∑ i : Fin n, q i * x i
            + r

def IsNonlinearConjugateGradientIteration
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ)
    (x : ℕ → E)
    (p : ℕ → E)
    (α : ℕ → ℝ)
    (β : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    x (k + 1) = x k + α k • p k ∧
      p (k + 1) = -gradient f (x (k + 1)) + β (k + 1) • p k

def PolakRibiereParameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  ⟪gradient f (x (k + 1)), gradient f (x (k + 1)) - gradient f (x k)⟫ /
    ‖gradient f (x k)‖ ^ 2

def HestenesStiefelParameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x p : ℕ → E) (k : ℕ) : ℝ :=
  ⟪gradient f (x (k + 1)), gradient f (x (k + 1)) - gradient f (x k)⟫ /
    ⟪gradient f (x (k + 1)) - gradient f (x k), p k⟫

def FletcherReevesParameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  ⟪gradient f (x (k + 1)), gradient f (x (k + 1))⟫ /
    ⟪gradient f (x k), gradient f (x k)⟫

theorem polakRibiere_and_hestenesStiefel_eq_fletcherReeves_for_quadratic_exact_line_search
    {n : ℕ}
    [InnerProductSpace ℝ (Fin n → ℝ)]
    (f : (Fin n → ℝ) → ℝ)
    (x p : ℕ → (Fin n → ℝ))
    (α β : ℕ → ℝ)
    (k : ℕ)
    (hquad : IsQuadraticFunction f)
    (hcg : IsNonlinearConjugateGradientIteration f x p α β)
    (hexact : IsExactLineSearch f (x k) (p k) (α k))
    (hgrad_ne : gradient f (x k) ≠ 0) :
    PolakRibiereParameter f x k = FletcherReevesParameter f x k ∧
      HestenesStiefelParameter f x p k = FletcherReevesParameter f x k := by
  sorry

end «CAM-Bench-122»
