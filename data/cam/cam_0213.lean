import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-213»

def IsSeparableConcaveMaximizationProblem
    {n : ℕ} (f : Fin n → ℝ → ℝ) (objective : (Fin n → ℝ) → ℝ) : Prop :=
  objective = (fun x => ∑ i : Fin n, f i (x i)) ∧
    ∀ i : Fin n, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (f i)

def SatisfiesKKTConditions
    {n m : ℕ}
    (_f : (Fin n → ℝ) → ℝ)
    (g : Fin m → (Fin n → ℝ) → ℝ)
    (gradF : (Fin n → ℝ) → Fin n → ℝ)
    (gradG : Fin m → (Fin n → ℝ) → Fin n → ℝ)
    (x : Fin n → ℝ)
    (μ : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, g i x ≤ 0) ∧
  (∀ i : Fin m, 0 ≤ μ i) ∧
  (∀ i : Fin m, μ i * g i x = 0) ∧
  (∀ j : Fin n, gradF x j + ∑ i : Fin m, μ i * gradG i x j = 0)

structure ResourceAllocationObjective where
  n : ℕ
  a : Fin n → ℝ
  pi : Fin n → ℝ
  c : ℝ
  B : ℝ
  U : ℝ → ℝ
  ha_pos : ∀ i : Fin n, 0 < a i
  hpi_nonneg : ∀ i : Fin n, 0 ≤ pi i
  hpi_sum : ∑ i : Fin n, pi i = 1
  hc_mem : c ∈ Set.Ioo (0 : ℝ) 1
  hB_nonneg : 0 ≤ B
  hU_mono : Monotone U
  hU_strictConcave : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) U
  hU_zero : U 0 = 0

def ResourceAllocationObjective.P (r : ResourceAllocationObjective) : ℝ :=
  (1 - ResourceAllocationObjective.c r) *
    ((∑ i : Fin (ResourceAllocationObjective.n r), ResourceAllocationObjective.a r i) +
      ResourceAllocationObjective.B r)

def ResourceAllocationObjective.p (r : ResourceAllocationObjective)
    (x : Fin (ResourceAllocationObjective.n r) → ℝ) (i : Fin (ResourceAllocationObjective.n r)) : ℝ :=
  (x i / (x i + ResourceAllocationObjective.a r i)) * ResourceAllocationObjective.P r

def ResourceAllocationObjective.feasible (r : ResourceAllocationObjective)
    (x : Fin (ResourceAllocationObjective.n r) → ℝ) : Prop :=
  (∀ i : Fin (ResourceAllocationObjective.n r), 0 ≤ x i) ∧
    ∑ i : Fin (ResourceAllocationObjective.n r), x i = ResourceAllocationObjective.B r

def ResourceAllocationObjective.objective (r : ResourceAllocationObjective)
    (x : Fin (ResourceAllocationObjective.n r) → ℝ) : ℝ :=
  ∑ i : Fin (ResourceAllocationObjective.n r),
    ResourceAllocationObjective.pi r i * ResourceAllocationObjective.U r (ResourceAllocationObjective.p r x i)

structure BudgetedUtilityMaximizationProblem where
  data : ResourceAllocationObjective

def BudgetedUtilityMaximizationProblem.feasible
    (p : BudgetedUtilityMaximizationProblem)
    (x : Fin p.data.n → ℝ) : Prop :=
  p.data.feasible x

def BudgetedUtilityMaximizationProblem.objective
    (p : BudgetedUtilityMaximizationProblem)
    (x : Fin p.data.n → ℝ) : ℝ :=
  p.data.objective x

def BudgetedUtilityMaximizationProblem.isSolution
    (p : BudgetedUtilityMaximizationProblem)
    (x : Fin p.data.n → ℝ) : Prop :=
  p.feasible x ∧ ∀ y : Fin p.data.n → ℝ, p.feasible y → p.objective y ≤ p.objective x

structure SeparableConcaveResourceAllocationProblem where
  data : ResourceAllocationObjective

def SeparableConcaveResourceAllocationProblem.f
    (p : SeparableConcaveResourceAllocationProblem)
    (i : Fin p.data.n) (t : ℝ) : ℝ :=
  p.data.pi i * p.data.U (((1 - p.data.c) * ((∑ j : Fin p.data.n, p.data.a j) + p.data.B)) * (t / (t + p.data.a i)))

def SeparableConcaveResourceAllocationProblem.feasible
    (p : SeparableConcaveResourceAllocationProblem)
    (x : Fin p.data.n → ℝ) : Prop :=
  (∀ i : Fin p.data.n, 0 ≤ x i) ∧
    ∑ i : Fin p.data.n, x i = p.data.B

def SeparableConcaveResourceAllocationProblem.objective
    (p : SeparableConcaveResourceAllocationProblem)
    (x : Fin p.data.n → ℝ) : ℝ :=
  ∑ i : Fin p.data.n, p.f i (x i)

def SeparableConcaveResourceAllocationProblem.isSeparableConcaveMaximizationProblem
    (p : SeparableConcaveResourceAllocationProblem) : Prop :=
  IsSeparableConcaveMaximizationProblem p.f p.objective

def SeparableConcaveResourceAllocationProblem.isSolution
    (p : SeparableConcaveResourceAllocationProblem)
    (x : Fin p.data.n → ℝ) : Prop :=
  p.feasible x ∧
    ∀ y : Fin p.data.n → ℝ, p.feasible y → p.objective y ≤ p.objective x

theorem resource_allocation_equiv_separable_concave_unique_solution
    (p : SeparableConcaveResourceAllocationProblem)
    (hconcave : ∀ i : Fin p.data.n, StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) (p.f i)) :
    IsSeparableConcaveMaximizationProblem p.f p.objective ∧
      (∀ x : Fin p.data.n → ℝ,
        p.feasible x →
          p.data.objective x = p.objective x) ∧
      (∀ x : Fin p.data.n → ℝ,
        (({ data := p.data } : BudgetedUtilityMaximizationProblem).isSolution x ↔
          p.isSolution x)) ∧
      (∀ x y : Fin p.data.n → ℝ,
        p.isSolution x → p.isSolution y → x = y) := by
  sorry

end «CAM-Bench-213»
