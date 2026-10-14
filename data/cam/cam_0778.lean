import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-778»

def IsClosedConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty (Set.range f) ∧
  f ⁻¹' {⊤} = ∅ ∧
  LowerSemicontinuous f ∧
  Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

open scoped RealInnerProductSpace

def FenchelConjugate {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun y => sSup {z : EReal | ∃ x : EuclideanSpace ℝ (Fin n), z = (⟪y, x⟫ : ℝ) - f x}

def ProximalMapping {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal) (μ : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {u | 0 < μ ∧ IsMinOn (fun v => g v + ((1 / (2 * μ)) * ‖v - z‖ ^ 2 : ℝ)) Set.univ u}

theorem moreau_decomposition
    {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : IsClosedConvexFunction f)
    {lam : ℝ}
    (hlam : 0 < lam)
    (x : Fin n → ℝ) :
    let prox_f :=
      ProximalMapping
        (fun y : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) y))
        lam
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let prox_fc :=
      ProximalMapping
        (FenchelConjugate
          (fun y : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) y)))
        (lam⁻¹)
        ((1 / lam) • ((EuclideanSpace.equiv (Fin n) ℝ).symm x))
    ∃ u ∈ prox_f, ∃ v ∈ prox_fc,
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) = u + lam • v := by
  sorry

end «CAM-Bench-778»
