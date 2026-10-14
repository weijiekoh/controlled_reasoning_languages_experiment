import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-615»

open scoped BigOperators

def IsMonomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ a : Fin n → ℝ,
      ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 < x j) →
        f x = c * ∏ j : Fin n, Real.rpow (x j) (a j)

def IsPosynomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧
    ∃ g : Fin K → ((Fin n → ℝ) → ℝ),
      (∀ k : Fin K, IsMonomial (g k)) ∧
      ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 < x j) →
        f x = ∑ k : Fin K, g k x

def IsSignomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ K : ℕ,
    ∃ g : Fin K → ((Fin n → ℝ) → ℝ),
      ∃ w : Fin K → ℝ,
        (∀ k : Fin K, IsMonomial (g k)) ∧
        ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 < x j) →
          f x = ∑ k : Fin K, w k * g k x

def GeometricProgramFeasible {n m p : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ)
    (f : Fin m → ((Fin n → ℝ) → ℝ))
    (g : Fin p → ((Fin n → ℝ) → ℝ)) : (Fin n → ℝ) → Prop :=
  fun x =>
    IsPosynomial f₀ ∧
    (∀ i : Fin m, IsPosynomial (f i)) ∧
    (∀ i : Fin p, IsMonomial (g i)) ∧
    (∀ j : Fin n, 0 < x j) ∧
    (∀ i : Fin m, f i x ≤ 1) ∧
    (∀ i : Fin p, g i x = 1)

def IsGeometricProgram {n m p : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ)
    (f : Fin m → ((Fin n → ℝ) → ℝ))
    (g : Fin p → ((Fin n → ℝ) → ℝ)) : Prop :=
  IsPosynomial f₀ ∧
  (∀ i : Fin m, IsPosynomial (f i)) ∧
  (∀ i : Fin p, IsMonomial (g i))

structure SignomialOptimizationProblem where
  n : ℕ
  m : ℕ
  p : ℕ
  objective : (Fin n → ℝ) → ℝ
  ineqConstr : Fin m → ((Fin n → ℝ) → ℝ)
  eqConstr : Fin p → ((Fin n → ℝ) → ℝ)
  posDomain : (Fin n → ℝ) → Prop
  posDomain_spec : ∀ x : Fin n → ℝ, posDomain x ↔ ∀ j : Fin n, 0 < x j

theorem signomial_problem_equiv_geometric_program
    {n m p : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ)
    (f : Fin m → ((Fin n → ℝ) → ℝ))
    (h : Fin p → ((Fin n → ℝ) → ℝ))
    (pFun : Fin m → ((Fin n → ℝ) → ℝ))
    (qFun : Fin m → ((Fin n → ℝ) → ℝ))
    (rFun : Fin p → ((Fin n → ℝ) → ℝ))
    (sFun : Fin p → ((Fin n → ℝ) → ℝ))
    (hf₀ : IsPosynomial f₀)
    (hp : ∀ i : Fin m, IsPosynomial (pFun i))
    (hq : ∀ i : Fin m, IsMonomial (qFun i))
    (hf : ∀ i : Fin m, f i = fun x => pFun i x - qFun i x)
    (hr : ∀ i : Fin p, IsMonomial (rFun i))
    (hs : ∀ i : Fin p, IsMonomial (sFun i))
    (hh : ∀ i : Fin p, h i = fun x => rFun i x - sFun i x) :
    IsGeometricProgram f₀
      (fun i x => pFun i x / qFun i x)
      (fun i x => rFun i x / sFun i x) ∧
    ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 < x j) →
      ((∀ i : Fin m, f i x ≤ 0 ↔ pFun i x / qFun i x ≤ 1) ∧
       (∀ i : Fin p, h i x = 0 ↔ rFun i x / sFun i x = 1)) := by
  sorry

end «CAM-Bench-615»
