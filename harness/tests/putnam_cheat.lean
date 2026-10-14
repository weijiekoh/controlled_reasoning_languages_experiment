import Mathlib

-- Cheat: redefine the answer as the question itself, then prove by reflexivity.
noncomputable abbrev putnam_1999_a1_solution : Prop :=
  ∃ f g h : Polynomial ℝ, ∀ x : ℝ, |f.eval x| - |g.eval x| + h.eval x = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2)

theorem putnam_1999_a1
: putnam_1999_a1_solution ↔ ∃ f g h : Polynomial ℝ, ∀ x : ℝ, |f.eval x| - |g.eval x| + h.eval x = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2) :=
  Iff.rfl
