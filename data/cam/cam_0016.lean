import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-16»

def IsActiveConstraint {α : Type _} (g : α → ℝ) (x : α) : Prop :=
  g x = 0

def IsFeasiblePoint {α ι : Type _} (g : ι → α → ℝ) (x : α) : Prop :=
  ∀ i : ι, g i x ≥ 0

def ConstrainedQuarticMinimization : (ℝ × ℝ → ℝ) × (Fin 4 → (ℝ × ℝ → ℝ)) :=
  (fun x => (x.1 - (3 : ℝ) / 2) ^ 2 + (x.2 - 1) ^ 4,
   fun
    | ⟨0, _⟩ => fun x => 1 - x.1 - x.2
    | ⟨1, _⟩ => fun x => 1 - x.1 + x.2
    | ⟨2, _⟩ => fun x => 1 + x.1 - x.2
    | ⟨3, _⟩ => fun x => 1 + x.1 + x.2)

def constrainedQuarticConstraints : Fin 4 → (ℝ × ℝ → ℝ)
  | ⟨0, _⟩ => fun x => 1 - x.1 - x.2
  | ⟨1, _⟩ => fun x => 1 - x.1 + x.2
  | ⟨2, _⟩ => fun x => 1 + x.1 - x.2
  | ⟨3, _⟩ => fun x => 1 + x.1 + x.2

def ConstrainedQuarticMinimization.default :
    (ℝ × ℝ → ℝ) × (Fin 4 → (ℝ × ℝ → ℝ)) :=
  ConstrainedQuarticMinimization

def ConstrainedQuarticMinimization.isFeasible
    (p : (ℝ × ℝ → ℝ) × (Fin 4 → (ℝ × ℝ → ℝ))) (x : ℝ × ℝ) : Prop :=
  ∀ i : Fin 4, p.2 i x ≥ 0

def ConstrainedQuarticMinimization.isActive
    (p : (ℝ × ℝ → ℝ) × (Fin 4 → (ℝ × ℝ → ℝ))) (i : Fin 4) (x : ℝ × ℝ) : Prop :=
  p.2 i x = 0

def ConstrainedQuarticMinimization.objectiveValue
    (p : (ℝ × ℝ → ℝ) × (Fin 4 → (ℝ × ℝ → ℝ))) (x : ℝ × ℝ) : ℝ :=
  p.1 x

theorem only_first_constraint_active_at_solution :
    let p := ConstrainedQuarticMinimization.default
    let x : ℝ × ℝ := (1 / 2, 1 / 2)
    (∀ y : ℝ × ℝ,
        ConstrainedQuarticMinimization.isFeasible p y →
        ConstrainedQuarticMinimization.objectiveValue p x ≤
          ConstrainedQuarticMinimization.objectiveValue p y) ∧
      ConstrainedQuarticMinimization.isFeasible p x ∧
      ConstrainedQuarticMinimization.isActive p ⟨0, by decide⟩ x ∧
      ¬ ConstrainedQuarticMinimization.isActive p ⟨1, by decide⟩ x ∧
      ¬ ConstrainedQuarticMinimization.isActive p ⟨2, by decide⟩ x ∧
      ¬ ConstrainedQuarticMinimization.isActive p ⟨3, by decide⟩ x := by
  sorry

end «CAM-Bench-16»
