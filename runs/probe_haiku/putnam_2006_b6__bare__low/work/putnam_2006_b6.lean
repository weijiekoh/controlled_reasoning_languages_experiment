import Mathlib

open Set Topology Filter

noncomputable abbrev putnam_2006_b6_solution : ℕ → ℝ := fun k => ((k+1)/k)^k
/--
Let $k$ be an integer greater than 1. Suppose $a_0 > 0$, and define \[ a_{n+1} = a_n + \frac{1}{\sqrt[k]{a_n}} \] for $n > 0$. Evaluate \[\lim_{n \to \infty} \frac{a_n^{k+1}}{n^k}.\]
-/
theorem putnam_2006_b6
(k : ℕ)
(hk : k > 1)
(a : ℕ → ℝ)
(ha0 : a 0 > 0)
(ha : ∀ n : ℕ, a (n + 1) = a n + 1/((a n)^((1 : ℝ)/k)))
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (putnam_2006_b6_solution k)) := by
  have hKpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hKne : (k:ℝ) ≠ 0 := ne_of_gt hKpos
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have : 0 < 1/((a m)^((1:ℝ)/k)) := div_pos one_pos (Real.rpow_pos_of_pos ih _)
      linarith
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro n
    rw [ha n]
    have : 0 < 1/((a n)^((1:ℝ)/k)) := div_pos one_pos (Real.rpow_pos_of_pos (hpos n) _)
    linarith
  have hlim : Tendsto a atTop atTop := by
    apply tendsto_atTop_atTop_of_monotone hmono
    intro b
    by_contra hcon
    push Not at hcon
    have hb : 0 < b := lt_of_lt_of_le (hpos 0) (hcon 0).le
    have hcpos : 0 < 1/ b^((1:ℝ)/k) := div_pos one_pos (Real.rpow_pos_of_pos hb _)
    have key : ∀ n:ℕ, a 0 + n * (1/ b^((1:ℝ)/k)) ≤ a n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [ha m]
        have h1 : (a m)^((1:ℝ)/k) ≤ b^((1:ℝ)/k) :=
          Real.rpow_le_rpow (hpos m).le (hcon m).le (by positivity)
        have h2 : 1/ b^((1:ℝ)/k) ≤ 1/(a m)^((1:ℝ)/k) :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hpos m) _) h1
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (b / (1/ b^((1:ℝ)/k)))
    have h4 : b < n * (1/ b^((1:ℝ)/k)) := by rwa [div_lt_iff₀ hcpos] at hn
    have h3 := key n
    linarith [hpos 0, hcon n]
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((k:ℝ)+1)/k := ⟨_, rfl⟩
  have hp1 : p - 1 = 1/(k:ℝ) := by
    rw [hp, div_sub_one hKne]
    congr 1
    ring
  have hpk : p * (k:ℝ) = (k:ℝ) + 1 := by
    rw [hp]; field_simp
  have hp0 : 0 < p := by rw [hp]; positivity
  -- one step: a(n+1)^p - a n^p = p * (ξ / a n^(1/k)) with a n^(1/k) ≤ ξ ≤ a(n+1)^(1/k)
  have hstep : ∀ n, ∃ ξ : ℝ, (a n)^((1:ℝ)/k) ≤ ξ ∧ ξ ≤ (a (n+1))^((1:ℝ)/k) ∧
      (a (n+1))^p - (a n)^p = p * (ξ / (a n)^((1:ℝ)/k)) := by
    intro n
    have hx := hpos n
    have hy : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos hx _
    have hε : 0 < 1/(a n)^((1:ℝ)/k) := div_pos one_pos hy
    have hab : a n < a n + 1/(a n)^((1:ℝ)/k) := by linarith
    have hcont : ContinuousOn (fun t : ℝ => t^p) (Set.Icc (a n) (a n + 1/(a n)^((1:ℝ)/k))) := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hx ht.1
      exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt htpos))).continuousAt.continuousWithinAt
    have hder : ∀ t ∈ Set.Ioo (a n) (a n + 1/(a n)^((1:ℝ)/k)),
        HasDerivAt (fun t : ℝ => t^p) ((fun t : ℝ => p * t^(p-1)) t) t := by
      intro t ht
      have htpos : 0 < t := lt_trans hx ht.1
      exact Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt htpos))
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hab hcont hder
    have hsub : a n + 1/(a n)^((1:ℝ)/k) - a n = 1/(a n)^((1:ℝ)/k) := by ring
    rw [hsub, hp1, eq_div_iff (ne_of_gt hε)] at hξeq
    have hξpos : 0 < ξ := lt_trans hx hξ.1
    refine ⟨ξ^((1:ℝ)/k), ?_, ?_, ?_⟩
    · apply Real.rpow_le_rpow hx.le hξ.1.le (by positivity)
    · rw [ha n]
      apply Real.rpow_le_rpow hξpos.le hξ.2.le (by positivity)
    · rw [ha n]
      rw [← hξeq]
      field_simp
  have hdlow : ∀ n, p ≤ (a (n+1))^p - (a n)^p := by
    intro n
    obtain ⟨ξ, h1, _, h3⟩ := hstep n
    rw [h3]
    have hy : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos (hpos n) _
    have : 1 ≤ ξ / (a n)^((1:ℝ)/k) := (one_le_div hy).mpr h1
    have := mul_le_mul_of_nonneg_left this hp0.le
    linarith
  have hdup : ∀ n, (a (n+1))^p - (a n)^p ≤ p * ((a (n+1)) / a n)^((1:ℝ)/k) := by
    intro n
    obtain ⟨ξ, _, h2, h3⟩ := hstep n
    rw [h3, Real.div_rpow (hpos (n+1)).le (hpos n).le]
    have hy : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos (hpos n) _
    have : ξ / (a n)^((1:ℝ)/k) ≤ (a (n+1))^((1:ℝ)/k) / (a n)^((1:ℝ)/k) := by
      gcongr
    have := mul_le_mul_of_nonneg_left this hp0.le
    linarith
  -- ratio tends to 1
  have hratio : Tendsto (fun n => (a (n+1)) / a n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => a n * (a n)^((1:ℝ)/k)) atTop atTop :=
      Tendsto.atTop_mul_atTop₀ hlim ((tendsto_rpow_atTop (by positivity : (0:ℝ) < 1/k)).comp hlim)
    have h2 : Tendsto (fun n => (a n * (a n)^((1:ℝ)/k))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := (tendsto_const_nhds (x := (1:ℝ))).add h2
    rw [add_zero] at h3
    refine h3.congr (fun n => ?_)
    have hx := hpos n
    have hy : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos hx _
    rw [ha n]
    field_simp
  have hrt : Tendsto (fun n => ((a (n+1)) / a n)^((1:ℝ)/k)) atTop (𝓝 1) := by
    have := hratio.rpow_const (p := (1:ℝ)/k) (Or.inr (by positivity))
    simpa using this
  have hU : Tendsto (fun n => p * ((a (n+1)) / a n)^((1:ℝ)/k)) atTop (𝓝 p) := by
    have := (tendsto_const_nhds (x := p)).mul hrt
    simpa using this
  have hd : Tendsto (fun n => (a (n+1))^p - (a n)^p) atTop (𝓝 p) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU hdlow hdup
  have hC := hd.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, ((a (i+1))^p - (a i)^p) = (a n)^p - (a 0)^p := by
    intro n
    exact Finset.sum_range_sub (fun n => (a n)^p) n
  have h0 : Tendsto (fun n:ℕ => (a 0)^p * (n:ℝ)⁻¹) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat ((a 0)^p)
    simpa [div_eq_mul_inv] using this
  have hS : Tendsto (fun n:ℕ => (a n)^p / (n:ℝ)) atTop (𝓝 p) := by
    have := h0.add hC
    rw [zero_add] at this
    refine this.congr (fun n => ?_)
    rw [hsum n]
    ring
  have hF := hS.pow k
  have hconv : ∀ n:ℕ, ((a n)^p / (n:ℝ))^k = (a n)^(k+1) / (n:ℝ)^k := by
    intro n
    rw [div_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos n).le, hpk]
    norm_cast
  have hlimv : p^k = putnam_2006_b6_solution k := by
    rw [hp]
  refine (hlimv ▸ hF).congr (fun n => ?_)
  exact hconv n
