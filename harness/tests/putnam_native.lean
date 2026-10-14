import Mathlib

noncomputable abbrev putnam_1999_a1_solution : Prop := True

open Polynomial in
/-- Helper: the explicit witnesses satisfy the pointwise identity. -/
lemma putnam_1999_a1_key (x : ℝ) :
    |((C (3/2 : ℝ) * (X + 1) : Polynomial ℝ)).eval x| - |((C (5/2 : ℝ) * X : Polynomial ℝ)).eval x|
      + ((-X + C (1/2 : ℝ) : Polynomial ℝ)).eval x
      = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2) := by
  simp only [eval_mul, eval_C, eval_add, eval_X, eval_one, eval_neg]
  split_ifs with h1 h2
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring

open Polynomial in
theorem two_nat : (2:ℕ) + 2 = 4 := by native_decide

theorem putnam_1999_a1
: putnam_1999_a1_solution ↔ ∃ f g h : Polynomial ℝ, ∀ x : ℝ, |f.eval x| - |g.eval x| + h.eval x = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2) := by
  have := two_nat
  simp only [putnam_1999_a1_solution, true_iff]
  exact ⟨_, _, _, putnam_1999_a1_key⟩
