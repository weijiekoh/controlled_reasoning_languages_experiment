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
  refine ⟨fun _ => trivial, fun _ => ⟨0, ?_⟩⟩
  set b : ℕ → ℝ := fun n => exp (a n) with hb
  have hstep : ∀ n, b (n+1) = b n * exp (1 / b n) := by
    intro n
    simp only [hb, han, Real.exp_add, one_div, ← Real.exp_neg]
  have hpos : ∀ n, 0 < b n := fun n => Real.exp_pos _
  have hd : ∀ n, 1 ≤ b (n+1) - b n := by
    intro n
    have h := Real.add_one_le_exp (1 / b n)
    have := hpos n
    rw [hstep]
    have : b n * (1 / b n + 1) ≤ b n * exp (1 / b n) := by gcongr
    field_simp at this ⊢
    linarith
  have hge : ∀ n : ℕ, (n:ℝ) + 1 ≤ b n := by
    intro n
    induction n with
    | zero => simp [hb, ha0]
    | succ k ih => push_cast; linarith [hd k]
  have hinf : Tendsto b atTop atTop :=
    tendsto_atTop_mono hge (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hder := (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hy : Tendsto (fun n => 1 / b n) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(hinf.inv_tendsto_atTop).congr (fun n => by simp [one_div]), Eventually.of_forall fun n => ?_⟩
    have := hpos n
    simp; positivity
  have hlim := hder.comp hy
  rw [Real.exp_zero] at hlim
  have hdl : Tendsto (fun n => b (n+1) - b n) atTop (𝓝 1) := by
    refine hlim.congr fun n => ?_
    have := (hpos n).ne'
    simp only [Function.comp, zero_add, smul_eq_mul, hstep]
    field_simp
  have hc := hdl.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (b (i+1) - b i) = b n - b 0 :=
    fun n => Finset.sum_range_sub b n
  have hz : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * b 0) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (b 0)
  have h0 := hc.add hz
  have h1 : Tendsto (fun n : ℕ => b n / n) atTop (𝓝 1) := by
    rw [add_zero] at h0
    refine h0.congr' (Eventually.of_forall fun n => ?_)
    rw [hsum]; field_simp; ring
  have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, hb]
  rw [Real.log_div (hpos n).ne' hn'.ne', hb, Real.log_exp]
