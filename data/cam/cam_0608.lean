import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-608»

abbrev edom {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x < ⊤}

def CoordWiseLE {m : ℕ} (u v : Fin m → ℝ) : Prop :=
  ∀ i, u i ≤ v i

def CoordWiseLT {m : ℕ} (u v : Fin m → ℝ) : Prop :=
  ∀ i, u i < v i

noncomputable instance {m : ℕ} (u v : Fin m → ℝ) : Decidable (CoordWiseLT u v) :=
  Classical.dec _

def CoordWisePos {m : ℕ} (u : Fin m → ℝ) : Prop :=
  ∀ i, 0 < u i

abbrev unboundedBelow {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  sInf (f '' edom f) = ⊥

open scoped BigOperators

theorem f0_unboundedBelow_iff_exists_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hnonempty : ∃ x : Fin n → ℝ, CoordWiseLT (fun i => (A *ᵥ x) i) b) :
    let f₀ : (Fin n → ℝ) → EReal :=
      fun x =>
        if CoordWiseLT (fun i => (A *ᵥ x) i) b then
          -((∑ i : Fin m, Real.log (b i - (∑ j : Fin n, A i j * x j))) : ℝ)
        else
          ⊤
    unboundedBelow f₀ ↔
      ∃ v : Fin n → ℝ,
        CoordWiseLE (fun i => (A *ᵥ v) i) (fun _ => 0) ∧ (A *ᵥ v) ≠ 0 := by
  sorry

end «CAM-Bench-608»
