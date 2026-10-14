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
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) := by
  have hlow : ∀ n : ℕ, (n:ℝ) + exp 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ k ih =>
      rw [han k, Real.exp_add]
      have hy := Real.add_one_le_exp (exp (-a k))
      have hE := Real.exp_pos (a k)
      have hmul : exp (a k) * exp (-a k) = 1 := by rw [← Real.exp_add]; simp
      have h2 := mul_le_mul_of_nonneg_left hy hE.le
      push_cast
      nlinarith [Real.exp_pos (-a k)]
  have hnn : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    by_contra h
    push Not at h
    have h1 := Real.exp_lt_exp.mpr h
    rw [Real.exp_zero] at h1
    have := hlow n
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith [Real.exp_one_gt_d9]
  have hle1 : ∀ n : ℕ, exp (-a n) ≤ 1 := by
    intro n
    have := Real.exp_le_exp.mpr (show -a n ≤ 0 by linarith [hnn n])
    rwa [Real.exp_zero] at this
  have hup : ∀ n : ℕ, exp (a n) ≤ n + 4 * Real.sqrt ((n:ℝ)+1) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]; norm_num
      linarith [Real.exp_one_lt_d9]
    | succ k ih =>
      rw [han k, Real.exp_add]
      set E := exp (a k) with hEdef
      set y := exp (-a k) with hydef
      have hE := Real.exp_pos (a k)
      have hmul : E * y = 1 := by rw [hEdef, hydef, ← Real.exp_add]; simp
      have hEk : (k:ℝ) + 1 ≤ E := by linarith [hlow k, Real.exp_one_gt_d9]
      have hy0 : 0 ≤ y := (Real.exp_pos _).le
      have hy1 : y ≤ 1 := hle1 k
      have habs := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
      have hexp_le : exp y ≤ 1 + y + y^2 := by
        have := (abs_le.mp habs).2
        linarith
      have hstep : E * exp y ≤ E + 1 + y := by
        have h3 := mul_le_mul_of_nonneg_left hexp_le hE.le
        nlinarith
      have hyk : y * ((k:ℝ)+1) ≤ 1 := by nlinarith
      -- sqrt facts
      set p := Real.sqrt ((k:ℝ)+1) with hpdef
      set q := Real.sqrt ((k:ℝ)+1+1) with hqdef
      have hp2 : p^2 = (k:ℝ)+1 := Real.sq_sqrt (by positivity)
      have hq2 : q^2 = (k:ℝ)+1+1 := Real.sq_sqrt (by positivity)
      have hp0 : 0 ≤ p := Real.sqrt_nonneg _
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hp1 : 1 ≤ p := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hqp : q ≤ 2*p := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hpq : p < q := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hdiff : (q-p)*(q+p) = 1 := by nlinarith
      have hA : q + p ≤ 4*p^2 := by nlinarith
      have hB : 1 ≤ 4*p^2*(q-p) := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ q - p by linarith) (show (0:ℝ) ≤ 4*p^2 - (q+p) by linarith)]
      have hC : y ≤ 4*(q-p) := by
        by_contra hc
        push Not at hc
        have hp2pos : 0 < p^2 := by nlinarith
        nlinarith [mul_lt_mul_of_pos_left hc hp2pos]
      rw [Nat.cast_succ]
      have hsq : Real.sqrt ((k:ℝ)+1+1) = q := rfl
      rw [hsq]
      linarith [ih]
  have hg : Tendsto (fun n:ℕ => 8 / Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun n:ℕ => Real.sqrt (n:ℝ)) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨⌈max b 0 ^ 2⌉₊, fun n hn => ?_⟩
      have hn' : max b 0 ^ 2 ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
      have hs0 := Real.sqrt_nonneg (n:ℝ)
      have hsq := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
      nlinarith [le_max_left b 0, le_max_right b 0]
    have := (tendsto_const_nhds (x := (8:ℝ))).div_atTop hs
    simpa using this
  apply Iff.intro
  · intro _
    trivial
  · intro _
    refine ⟨0, ?_⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by linarith
      have h1 : (n:ℝ) ≤ exp (a n) := by linarith [hlow n, Real.exp_one_gt_d9]
      have := Real.log_le_log hnpos h1
      rw [Real.log_exp] at this
      show (0:ℝ) ≤ a n - Real.log n
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by linarith
      have hsn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
      have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
      have ht2 := Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
      have ht0 := Real.sqrt_nonneg ((n:ℝ)+1)
      have hts : Real.sqrt ((n:ℝ)+1) ≤ 2 * Real.sqrt (n:ℝ) := by
        nlinarith
      have hA := Real.log_le_log (Real.exp_pos _) (hup n)
      rw [Real.log_exp] at hA
      have hpos2 : (0:ℝ) < n + 4 * Real.sqrt ((n:ℝ)+1) := by positivity
      have hB : Real.log ((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) - Real.log n
          = Real.log (((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n) := by
        rw [Real.log_div hpos2.ne' hnpos.ne']
      have hC := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n by positivity)
      have hD : (((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n) - 1 = 4 * Real.sqrt ((n:ℝ)+1) / n := by
        field_simp
        ring
      have hE : 4 * Real.sqrt ((n:ℝ)+1) / n ≤ 8 / Real.sqrt (n:ℝ) := by
        rw [div_le_div_iff₀ hnpos hsn]
        nlinarith
      show a n - Real.log n ≤ 8 / Real.sqrt (n:ℝ)
      linarith
