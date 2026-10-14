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
  have hpos : ∀ n, 0 ≤ a n := by
    intro n
    induction n with
    | zero => rw [ha0]; norm_num
    | succ k ih => rw [han]; have := Real.exp_pos (-a k); linarith
  have hstep : ∀ n, exp (a (n+1)) = exp (a n) + exp (a n) * (exp (1 / exp (a n)) - 1) := by
    intro n
    have h1 : exp (-a n) = 1 / exp (a n) := by rw [Real.exp_neg, one_div]
    rw [han, Real.exp_add, h1]; ring
  have hinc_lo : ∀ n, 1 ≤ exp (a (n+1)) - exp (a n) := by
    intro n
    rw [hstep n]
    have hxp := Real.exp_pos (a n)
    have h3 : 1 / exp (a n) ≤ exp (1 / exp (a n)) - 1 := by
      have := Real.add_one_le_exp (1 / exp (a n)); linarith
    have h4 : exp (a n) * (1 / exp (a n)) ≤ exp (a n) * (exp (1 / exp (a n)) - 1) :=
      mul_le_mul_of_nonneg_left h3 hxp.le
    rw [mul_one_div_cancel hxp.ne'] at h4
    linarith
  have hinc_hi : ∀ n, exp (a (n+1)) - exp (a n) ≤ 1 + 1 / exp (a n) := by
    intro n
    rw [hstep n]
    have hxp := Real.exp_pos (a n)
    have hx1 : 1 ≤ exp (a n) := Real.one_le_exp (hpos n)
    have hle : 1 / exp (a n) ≤ 1 := by rw [div_le_one hxp]; exact hx1
    have hb := Real.abs_exp_sub_one_sub_id_le (x := 1 / exp (a n))
      (by rw [abs_of_nonneg (by positivity)]; exact hle)
    have hb2 := (abs_le.1 hb).2
    have key : exp (a n) * (exp (1 / exp (a n)) - 1) ≤ exp (a n) * (1 / exp (a n) + (1 / exp (a n))^2) :=
      mul_le_mul_of_nonneg_left (by linarith) hxp.le
    have e2 : exp (a n) * (1 / exp (a n) + (1 / exp (a n))^2) = 1 + 1 / exp (a n) := by
      field_simp
    linarith
  have hgrow : ∀ n : ℕ, (n:ℝ) ≤ exp (a n) := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero]; exact (Real.exp_pos _).le
    | succ k ih =>
      have := hinc_lo k
      push_cast
      linarith
  have hup : ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∃ c : ℝ, ∀ n : ℕ, N ≤ n → exp (a n) ≤ (1 + ε) * n + c := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine ⟨m+1, by omega, exp (a (m+1)) - ((m+1 : ℕ) : ℝ), ?_⟩
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have : (0:ℝ) ≤ ε * ((m+1 : ℕ) : ℝ) := by positivity
      linarith
    | succ k hk ih =>
      have hk2 : (m:ℝ) + 1 ≤ k := by
        have : ((m+1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        push_cast at this; exact this
      have hkpos : (0:ℝ) < k := by linarith [(by positivity : (0:ℝ) ≤ m)]
      have h1 : 1 / exp (a k) ≤ 1 / (k:ℝ) :=
        one_div_le_one_div_of_le hkpos (hgrow k)
      have h2 : 1 / (k:ℝ) ≤ 1 / ((m:ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hk2
      have hinc := hinc_hi k
      push_cast at ih
      have h4 : 1 / exp (a k) ≤ ε := by linarith
      push_cast
      linarith
  have hf : Tendsto (fun n : ℕ => exp (a n) / n) atTop (𝓝 1) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have : (1:ℝ) ≤ exp (a n) / n := by
        rw [le_div_iff₀ (by linarith)]; linarith [hgrow n]
      linarith
    · intro b hb
      obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (b - 1) / 2 := ⟨_, rfl⟩
      have hδpos : 0 < δ := by rw [hδ]; linarith
      obtain ⟨N, hN1, c, hcN⟩ := hup δ hδpos
      have hc : Tendsto (fun n : ℕ => c / (n:ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat c
      have hev := (tendsto_order.1 hc).2 δ hδpos
      have hb' : b = 1 + 2 * δ := by rw [hδ]; ring
      filter_upwards [hev, eventually_ge_atTop N] with n hcn hNn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans hN1 hNn)
      have hnpos : (0:ℝ) < n := by linarith
      have hbound := hcN n hNn
      have hcn' : c < δ * n := (div_lt_iff₀ hnpos).1 hcn
      rw [div_lt_iff₀ hnpos, hb']
      linarith
  have hlim : Tendsto (fun n : ℕ => a n - Real.log n) atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hf
    rw [Real.log_one] at hlog
    refine Tendsto.congr' ?_ hlog
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [Function.comp]
    rw [Real.log_div (Real.exp_pos _).ne' hn0, Real.log_exp]
  exact ⟨fun _ => trivial, fun _ => ⟨0, hlim⟩⟩
