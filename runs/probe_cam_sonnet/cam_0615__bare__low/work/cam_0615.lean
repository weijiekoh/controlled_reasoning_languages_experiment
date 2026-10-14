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

theorem mono_div {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (hf : IsMonomial f) (hg : IsMonomial g) :
    IsMonomial (fun x => f x / g x) := by
  obtain ⟨c, hc, a, ha⟩ := hf
  obtain ⟨d, hd, b, hb⟩ := hg
  refine ⟨c / d, div_pos hc hd, fun j => a j - b j, fun x hx => ?_⟩
  show f x / g x = _
  rw [ha x hx, hb x hx]
  have : ∏ j : Fin n, Real.rpow (x j) (a j - b j) = (∏ j : Fin n, Real.rpow (x j) (a j)) / ∏ j : Fin n, Real.rpow (x j) (b j) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl (fun j _ => Real.rpow_sub (hx j) _ _)
  rw [this]; ring

theorem mono_pos {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsMonomial f) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) : 0 < f x := by
  obtain ⟨c, hc, a, ha⟩ := hf
  rw [ha x hx]
  exact mul_pos hc (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hx j) _)

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
  have hpos := fun i x hx => mono_pos _ (hq i) x hx
  refine ⟨⟨hf₀, fun i => ?_, fun i => mono_div _ _ (hr i) (hs i)⟩, fun x hx => ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨K, hK, g, hg, hsum⟩ := hp i
    refine ⟨K, hK, fun k x => g k x / qFun i x, fun k => mono_div _ _ (hg k) (hq i), fun x hx => ?_⟩
    show pFun i x / qFun i x = _
    rw [hsum x hx, Finset.sum_div]
  · have := hpos i x hx
    rw [hf i, div_le_one this]
    constructor <;> intro h <;> simp only at * <;> linarith
  · have := mono_pos _ (hs i) x hx
    rw [hh i, div_eq_one_iff_eq this.ne']
    simp only [sub_eq_zero]

end «CAM-Bench-615»
