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
  have mpos : ∀ {k : Nat} (g : (Fin k → ℝ) → ℝ), IsMonomial g → ∀ x : Fin k → ℝ, (∀ j, 0 < x j) → 0 < g x := by
    intro k g ⟨c, hc, a, ha⟩ x hx
    rw [ha x hx]
    exact mul_pos hc (Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) _))
  have mdiv : ∀ {k : Nat} (g q : (Fin k → ℝ) → ℝ), IsMonomial g → IsMonomial q →
      IsMonomial (fun x => g x / q x) := by
    intro k g q ⟨c, hc, a, ha⟩ ⟨d, hd, b, hb⟩
    refine ⟨c / d, div_pos hc hd, fun j => a j - b j, ?_⟩
    intro x hx
    simp only
    rw [ha x hx, hb x hx]
    have e : ∏ j, (x j).rpow (a j - b j) = (∏ j, (x j).rpow (a j)) / ∏ j, (x j).rpow (b j) := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl (fun j _ => Real.rpow_sub (hx j) _ _)
    rw [e]
    have h1 : 0 < ∏ j, (x j).rpow (b j) := Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) _)
    field_simp
  have pdiv : ∀ {k : Nat} (P q : (Fin k → ℝ) → ℝ), IsPosynomial P → IsMonomial q →
      IsPosynomial (fun x => P x / q x) := by
    intro k P q ⟨K, hK, g, hg, hPg⟩ hq
    refine ⟨K, hK, fun i x => g i x / q x, fun i => mdiv _ _ (hg i) hq, ?_⟩
    intro x hx
    simp only
    rw [hPg x hx, Finset.sum_div]
  refine ⟨⟨hf₀, ?_, ?_⟩, ?_⟩
  · intro i
    exact pdiv _ _ (hp i) (hq i)
  · intro i
    exact mdiv _ _ (hr i) (hs i)
  · intro x hx
    constructor
    · intro i
      have hqpos := mpos _ (hq i) x hx
      rw [hf i, div_le_one hqpos]
      simp only
      constructor <;> intro h <;> linarith
    · intro i
      have hspos := mpos _ (hs i) x hx
      rw [hh i, div_eq_one_iff_eq hspos.ne']
      simp only
      constructor <;> intro h <;> linarith

end «CAM-Bench-615»
