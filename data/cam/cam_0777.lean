import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-777»

def proper {α : Type} (f : α → EReal) : Prop :=
  (∀ x : α, f x ≠ ⊥) ∧ ∃ x : α, f x ≠ ⊤

def closed {α : Type} [TopologicalSpace α] (f : α → EReal) : Prop :=
  IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : EReal)}

def fenchelConjugate (f : ℝ → EReal) : ℝ → EReal :=
  fun y => sSup {t : EReal | ∃ z : ℝ, t = ((y * z : ℝ) : EReal) - f z}

def proximalMapping (g : ℝ → EReal) (x : ℝ) : Set ℝ :=
  {u : ℝ | ∀ v : ℝ, g u + ((1 : EReal) / 2) * ((u - x) ^ 2 : ℝ) ≤ g v + ((1 : EReal) / 2) * ((v - x) ^ 2 : ℝ)}

def moreauDecomposition (f : ℝ → EReal) : Prop :=
  proper f →
    closed f →
      ConvexOn ℝ Set.univ (fun x => (f x).toReal) →
        ∀ x : ℝ,
          ∀ u ∈ proximalMapping f x,
            ∀ v ∈ proximalMapping (fenchelConjugate f) x,
              x = u + v

theorem moreau_decomposition_of_moreauDecomposition
    {f : ℝ → EReal} (hproper : proper f) (hclosed : closed f)
    (hconvex : ConvexOn ℝ Set.univ (fun x => (f x).toReal)) :
    ∀ x : ℝ, ∃ u v : ℝ,
      u ∈ proximalMapping f x ∧
      v ∈ proximalMapping (fenchelConjugate f) x ∧
      x = u + v := by
  sorry

end «CAM-Bench-777»
