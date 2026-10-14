import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-623»

variable {n : Type} [Fintype n] [DecidableEq n]

def IsGInvariant (𝒢 : Set (Matrix n n ℝ)) (f : (n → ℝ) → ℝ) : Prop :=
  ∀ ⦃Q : Matrix n n ℝ⦄, Q ∈ 𝒢 → ∀ x : n → ℝ, f (Q.mulVec x) = f x

def Fix (𝒢 : Set (Matrix n n ℝ)) : Submodule ℝ (n → ℝ) where
  carrier := { x | ∀ ⦃Q : Matrix n n ℝ⦄, Q ∈ 𝒢 → Q.mulVec x = x }
  add_mem' := by
    intro x y hx hy Q hQ
    simpa [Matrix.mulVec_add] using congrArg (fun z => z + Q.mulVec y) (hx hQ) |>.trans (by
      simpa [Matrix.mulVec_add, hy hQ])
  zero_mem' := by
    intro Q hQ
    simpa using (Matrix.mulVec_zero (A := Q))
  smul_mem' := by
    intro a x hx Q hQ
    simpa [Matrix.mulVec_smul] using congrArg (fun z => a • z) (hx hQ)

def IsConvex (f : (n → ℝ) → ℝ) : Prop :=
  ∀ u v : n → ℝ, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    f (lam • u + (1 - lam) • v) ≤ lam * f u + (1 - lam) * f v

theorem convex_GInvariant_avg_le
    {n : Type} [Fintype n] [DecidableEq n]
    (k : ℕ) (hk : k ≠ 0) (Q : Fin k → Matrix n n ℝ) (f : (n → ℝ) → ℝ)
    (hgroup : Subgroup (Matrix n n ℝ)ˣ)
    (hrange :
      Set.range Q =
        ((fun u : (Matrix n n ℝ)ˣ => (u : Matrix n n ℝ)) '' (hgroup : Set (Matrix n n ℝ)ˣ)))
    (hbij :
      Function.Bijective
        (fun i : Fin k =>
          (⟨Q i, by
            rw [← hrange]
            exact ⟨i, rfl⟩⟩ :
            {A : Matrix n n ℝ // A ∈
              ((fun u : (Matrix n n ℝ)ˣ => (u : Matrix n n ℝ)) '' (hgroup : Set (Matrix n n ℝ)ˣ))})))
    (hconv : ConvexOn ℝ Set.univ f)
    (hinv : IsGInvariant (n := n) (Set.range Q) f)
    (x : n → ℝ) :
    f ((1 / (k : ℝ)) • ∑ i : Fin k, (Q i).mulVec x) ≤ f x := by
  sorry

end «CAM-Bench-623»
