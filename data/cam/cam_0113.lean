import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-113»

def IsDescentDirection (f : ℝ → ℝ) (x p : ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧ deriv f x * p < 0

def SatisfiesGoldsteinConditions
    (f : ℝ → ℝ) (f' x p c α : ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧
  f' = deriv f x ∧
  0 < α ∧
  c ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
  f x + (1 - c) * α * (f' * p) ≤ f (x + α * p) ∧
  f (x + α * p) ≤ f x + c * α * (f' * p)

open scoped BigOperators

theorem quadratic_exact_line_search_satisfies_Goldstein
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) (b xk pk : n → ℝ) (γ c αk : ℝ)
    (hQsymm : Q.IsSymm)
    (hQpos : ∀ x : n → ℝ, x ≠ 0 → 0 < dotProduct x (fun i => ∑ j, Q i j * x j))
    (hdescent :
      dotProduct
        (fun i => ∑ j, Q i j * xk j + b i)
        pk < 0)
    (hαk :
      αk ∈ {a ∈ Set.Ici (0 : ℝ) |
        ∀ α ∈ Set.Ici (0 : ℝ),
          (1 / 2 : ℝ) *
              dotProduct
                (fun i => xk i + a * pk i)
                (fun i => ∑ j, Q i j * (xk j + a * pk j)) +
            dotProduct b (fun i => xk i + a * pk i) + γ ≤
          (1 / 2 : ℝ) *
              dotProduct
                (fun i => xk i + α * pk i)
                (fun i => ∑ j, Q i j * (xk j + α * pk j)) +
            dotProduct b (fun i => xk i + α * pk i) + γ})
    (hαk_pos : 0 < αk)
    (hc : c ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ((1 / 2 : ℝ) *
          dotProduct xk (fun i => ∑ j, Q i j * xk j) +
        dotProduct b xk + γ) +
      (1 - c) * αk *
        (dotProduct
          (fun i => ∑ j, Q i j * xk j + b i)
          pk) ≤
      (1 / 2 : ℝ) *
          dotProduct
            (fun i => xk i + αk * pk i)
            (fun i => ∑ j, Q i j * (xk j + αk * pk j)) +
        dotProduct b (fun i => xk i + αk * pk i) + γ ∧
    (1 / 2 : ℝ) *
          dotProduct
            (fun i => xk i + αk * pk i)
            (fun i => ∑ j, Q i j * (xk j + αk * pk j)) +
        dotProduct b (fun i => xk i + αk * pk i) + γ ≤
      ((1 / 2 : ℝ) *
          dotProduct xk (fun i => ∑ j, Q i j * xk j) +
        dotProduct b xk + γ) +
      c * αk *
        (dotProduct
          (fun i => ∑ j, Q i j * xk j + b i)
          pk) := by
  sorry

end «CAM-Bench-113»
