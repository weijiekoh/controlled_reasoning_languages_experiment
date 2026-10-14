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
  have hge : ∀ n, a n ≥ 1 := by
    intro n
    induction n with
    | zero => rw [ha0]
    | succ k ih => rw [han]; have := exp_pos (-a k); linarith
  have hlow : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => rw [ha0]; simp
    | succ k ih =>
      rw [han, Real.exp_add]
      have h1 : exp (-a k) + 1 ≤ exp (exp (-a k)) := Real.add_one_le_exp _
      have h2 : exp (a k) * exp (-a k) = 1 := by rw [← Real.exp_add]; simp
      have h3 := mul_le_mul_of_nonneg_left h1 (exp_pos (a k)).le
      push_cast
      nlinarith
  have hup : ∀ n : ℕ, exp (a n) ≤ n + exp 1 + 3 * Real.log ((n:ℝ)+2) := by
    intro n
    induction n with
    | zero =>
      have := Real.log_nonneg (show (1:ℝ) ≤ 0 + 2 by norm_num)
      rw [ha0]; push_cast; linarith
    | succ k ih =>
      have hk := hlow k
      have hgk := hge k
      set x := exp (-a k) with hxdef
      have hx_pos : 0 < x := exp_pos _
      have hx1 : x ≤ 1 := by
        rw [hxdef]; apply Real.exp_le_one_iff.mpr; linarith
      have hB : exp (a k) * x = 1 := by rw [hxdef, ← Real.exp_add]; simp
      have hxk : x * ((k:ℝ)+1) ≤ 1 := by nlinarith
      have hx3 : x * ((k:ℝ)+3) ≤ 3 := by nlinarith
      have hexp := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_pos hx_pos]; exact hx1)
      have hexp' : exp x ≤ 1 + x + x^2 := by
        have := (abs_le.mp hexp).2; linarith
      have hstep : exp (a (k+1)) ≤ exp (a k) + 1 + x := by
        rw [han, Real.exp_add]
        have h3 := mul_le_mul_of_nonneg_left hexp' (exp_pos (a k)).le
        have : exp (a k) * (1 + x + x^2) = exp (a k) + 1 + x := by
          have : exp (a k) * x ^ 2 = x := by nlinarith
          nlinarith
        linarith
      have hD : 1 ≤ ((k:ℝ)+3) * (Real.log ((k:ℝ)+3) - Real.log ((k:ℝ)+2)) := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((k:ℝ)+2)/((k:ℝ)+3) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have e1 : ((k:ℝ)+2)/((k:ℝ)+3) - 1 = -(1/((k:ℝ)+3)) := by field_simp; ring
        have e2 : (k:ℝ)+3 ≠ 0 := by positivity
        have : Real.log ((k:ℝ)+2) - Real.log ((k:ℝ)+3) ≤ -(1/((k:ℝ)+3)) := by linarith
        have e3 : (1:ℝ)/((k:ℝ)+3) * ((k:ℝ)+3) = 1 := by field_simp
        nlinarith
      have hxD : x ≤ 3 * (Real.log ((k:ℝ)+3) - Real.log ((k:ℝ)+2)) := by
        nlinarith
      push_cast
      have : Real.log ((k:ℝ)+1+2) = Real.log ((k:ℝ)+3) := by ring_nf
      rw [this]
      have : Real.log ((k:ℝ)+2) ≤ Real.log ((k:ℝ)+3) := Real.log_le_log (by positivity) (by linarith)
      linarith
  -- limit of b_n / n
  have hf : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlogl : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+2) / ((n:ℝ)+2)) atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_id_atTop.comp_tendsto hf).tendsto_div_nhds_zero
    simpa [Function.comp] using h
  have hA : Tendsto (fun n : ℕ => 3 * exp 1 / ((n:ℝ)+2)) atTop (𝓝 0) :=
    (tendsto_const_nhds).div_atTop hf
  have hB : Tendsto (fun n : ℕ => 3 * exp 1 / ((n:ℝ)+2) + 9 * (Real.log ((n:ℝ)+2) / ((n:ℝ)+2))) atTop (𝓝 0) := by
    have := hA.add (hlogl.const_mul 9)
    simpa using this
  have hB1 : Tendsto (fun n : ℕ => 1 + (3 * exp 1 / ((n:ℝ)+2) + 9 * (Real.log ((n:ℝ)+2) / ((n:ℝ)+2)))) atTop (𝓝 1) := by
    have := hB.const_add 1
    simpa using this
  have hbn : Tendsto (fun n : ℕ => exp (a n) / n) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn
      have h1 := hlow n
      rw [le_div_iff₀ hnpos]; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn
      have hn3 : (n:ℝ) + 2 ≤ 3 * n := by
        have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hu := hup n
      have hL : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
      have hpos2 : (0:ℝ) < (n:ℝ)+2 := by positivity
      rw [div_le_iff₀ hnpos]
      have eq : (1 + (3 * exp 1 / ((n:ℝ)+2) + 9 * (Real.log ((n:ℝ)+2) / ((n:ℝ)+2)))) * n
          = n + (3 * exp 1 * n) / ((n:ℝ)+2) + 9 * (Real.log ((n:ℝ)+2) * n / ((n:ℝ)+2)) := by
        field_simp; ring
      rw [eq]
      have q1 : (3 * exp 1 * n) / ((n:ℝ)+2) ≥ 3 * exp 1 / 3 * 1 := by
        rw [ge_iff_le, le_div_iff₀ hpos2]; nlinarith [exp_pos 1]
      have q2 : (Real.log ((n:ℝ)+2) * n) / ((n:ℝ)+2) ≥ Real.log ((n:ℝ)+2) / 3 := by
        rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hpos2]; nlinarith
      nlinarith
  have hlim : Tendsto (fun n : ℕ => Real.log (exp (a n) / n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => Real.log (exp (a n) / n)) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log one_ne_zero).tendsto.comp hbn
    rwa [Real.log_one] at h
  simp only [putnam_2012_b4_solution]
  refine ⟨fun _ => trivial, fun _ => ⟨0, ?_⟩⟩
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Real.log_div (exp_pos _).ne' hn0, Real.log_exp]
