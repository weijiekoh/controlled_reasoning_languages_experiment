import Mathlib

open Matrix Function Real Topology Filter

noncomputable abbrev putnam_2012_b4_solution : Prop := True
/--
Suppose that $a_0 = 1$ and that $a_{n+1} = a_n + e^{-a_n}$ for $n=0,1,2,\dots$. Does $a_n - \log n$
have a finite limit as $n \to \infty$? (Here $\log n = \log_e n = \ln n$.)
-/
theorem putnam_2012_b4
(a : ℕ → ℝ)
(ha0 : a 0 = 1)
(han : ∀ n : ℕ, a (n + 1) = a n + exp (-a n))
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) :=
by
  have hA : ∀ n, 1 ≤ a n := by
    intro n
    induction n with
    | zero => rw [ha0]
    | succ k ih => rw [han]; have := exp_pos (-a k); linarith
  have hX : ∀ n, exp (a n) * exp (-a n) = 1 := by
    intro n; rw [← exp_add]; simp
  have hstep : ∀ n, exp (a (n+1)) = exp (a n) * exp (exp (-a n)) := by
    intro n; rw [han, exp_add]
  have hsq : ∀ n : ℕ, 1 / ((n:ℝ)+1) ≤ 2 * (sqrt ((n:ℝ)+1) - sqrt n) := by
    intro n
    have h1 : sqrt ((n:ℝ)+1) ^ 2 = n+1 := sq_sqrt (by positivity)
    have h2 : sqrt (n:ℝ) ^ 2 = n := sq_sqrt (by positivity)
    have h3 : sqrt (n:ℝ) ≤ sqrt ((n:ℝ)+1) := sqrt_le_sqrt (by linarith)
    have h4 : 1 ≤ sqrt ((n:ℝ)+1) := by
      calc (1:ℝ) = sqrt 1 := sqrt_one.symm
        _ ≤ sqrt ((n:ℝ)+1) := sqrt_le_sqrt (by linarith)
    have h0 : 0 ≤ sqrt (n:ℝ) := sqrt_nonneg _
    have h5 : 1 ≤ 2 * (sqrt ((n:ℝ)+1) - sqrt n) * sqrt ((n:ℝ)+1) := by
      nlinarith [sq_nonneg (sqrt ((n:ℝ)+1) - sqrt n)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hbound : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) ∧ exp (a n) ≤ n + 3 + 2 * sqrt n := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, ha0, sqrt_zero, mul_zero, add_zero, zero_add]
      constructor <;> linarith [add_one_le_exp (1:ℝ), exp_one_lt_d9]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have hs := hstep k
      have hBX := hX k
      have hsq' := hsq k
      set B := exp (a k) with hBdef
      set X := exp (-a k) with hXdef
      have hXpos : 0 < X := exp_pos _
      have hB0 : 0 ≤ B := by linarith
      have hX1 : X ≤ 1 := by nlinarith
      have hexpX : exp X ≤ 1 + X + X^2 := by
        have := Real.abs_exp_sub_one_sub_id_le (x := X) (by rw [abs_of_pos hXpos]; exact hX1)
        have := le_abs_self (exp X - 1 - X)
        linarith
      have hexpX' : 1 + X ≤ exp X := by linarith [add_one_le_exp X]
      rw [hs]
      push_cast
      constructor
      · have := mul_le_mul_of_nonneg_left hexpX' hB0
        nlinarith
      · have hXle : X ≤ 2 * (sqrt ((k:ℝ)+1) - sqrt k) := by
          have h6 : X * ((k:ℝ)+1) ≤ 1 := by nlinarith
          have h7 : X ≤ 1 / ((k:ℝ)+1) := by
            rw [le_div_iff₀ (by positivity)]; linarith
          linarith
        have hmul : B * exp X ≤ B * (1 + X + X^2) := mul_le_mul_of_nonneg_left hexpX hB0
        have e1 : B * (1 + X + X^2) = B + 1 + X := by linear_combination (X + 1) * hBX
        linarith
  have hlow : ∀ n : ℕ, 0 ≤ a n - log n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [Nat.cast_zero, Real.log_zero, sub_zero]; linarith [hA 0]
    · have hn : (n:ℝ) ≤ exp (a n) := by linarith [(hbound n).1]
      have hpos : (0:ℝ) < n := by exact_mod_cast h
      have : log (n:ℝ) ≤ log (exp (a n)) := log_le_log hpos hn
      rw [log_exp] at this; linarith
  have hup : ∀ n : ℕ, 1 ≤ n → a n - log n ≤ 5 / sqrt n := by
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hB := (hbound n).2
    have h1 : a n - log n = log (exp (a n) / n) := by
      rw [log_div (exp_pos _).ne' hnpos.ne', log_exp]
    rw [h1]
    have h2 := Real.log_le_sub_one_of_pos (show 0 < exp (a n) / n from div_pos (exp_pos _) hnpos)
    have hs : sqrt (n:ℝ) ^ 2 = n := sq_sqrt (by positivity)
    have hs1 : 1 ≤ sqrt (n:ℝ) := by
      rw [show (1:ℝ) = sqrt 1 from sqrt_one.symm]; exact sqrt_le_sqrt (by exact_mod_cast hn)
    have hsp : 0 < sqrt (n:ℝ) := by linarith
    calc log (exp (a n) / n) ≤ exp (a n) / n - 1 := h2
      _ ≤ 5 / sqrt n := by
        rw [div_sub_one hnpos.ne', div_le_div_iff₀ hnpos hsp]
        nlinarith [mul_le_mul_of_nonneg_right (show exp (a n) - n ≤ 3 + 2 * sqrt n by linarith) hsp.le]
  have hg : Tendsto (fun n : ℕ => 5 / sqrt (n:ℝ)) atTop (𝓝 0) := by
    have := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop this
  constructor
  · intro _; exact trivial
  · intro _
    refine ⟨0, ?_⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Filter.Eventually.of_forall hlow)
      (Filter.eventually_atTop.2 ⟨1, fun n hn => hup n hn⟩)
