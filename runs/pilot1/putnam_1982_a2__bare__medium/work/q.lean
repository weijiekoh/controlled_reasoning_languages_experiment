import Mathlib

open Set Function Filter Topology Polynomial Real

lemma key (m : ℕ) : (∑ k ∈ Finset.Icc 1 (m+3), (k:ℝ) ^ (logb (↑(m+3):ℝ) 2)) / (((m+3:ℕ):ℝ) * logb 2 ((m+3:ℕ):ℝ))^2
   ≤ 2 * (log 2)^2 * (1/log ((m+2:ℕ):ℝ) - 1/log ((m+3:ℕ):ℝ)) := by
  set n : ℝ := ((m+3:ℕ):ℝ) with hn
  have hn3 : (3:ℝ) ≤ n := by rw [hn]; push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hn2 : ((m+2:ℕ):ℝ) = n - 1 := by rw [hn]; push_cast; ring
  rw [hn2]
  have hl : 0 < log (n-1) := Real.log_pos (by linarith)
  have hl2 : log (n-1) ≤ log n := Real.log_le_log (by linarith) (by linarith)
  have hln : 0 < log n := lt_of_lt_of_le hl hl2
  have hl2p : 0 < log 2 := Real.log_pos (by norm_num)
  have hx : 0 < logb n 2 := Real.logb_pos (by linarith) (by norm_num)
  have hx1 : logb n 2 ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by linarith) (by norm_num)]; simpa using (by linarith : (2:ℝ) ≤ n)
  have hs : ∑ k ∈ Finset.Icc 1 (m+3), (k:ℝ) ^ (logb n 2) ≤ 2 * n := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 (m+3), (2:ℝ) := by
          apply Finset.sum_le_sum; intro k hk
          have hk' : (k:ℝ) ≤ n := by rw [hn]; exact_mod_cast (Finset.mem_Icc.mp hk).2
          calc (k:ℝ) ^ (logb n 2) ≤ n ^ (logb n 2) := Real.rpow_le_rpow (by positivity) hk' hx.le
            _ = 2 := Real.rpow_logb (by linarith) (by linarith) (by norm_num)
      _ = 2 * n := by simp [hn]; ring
  have hlog : 1/n ≤ log n - log (n-1) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (n-1)/n by apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith)] at this
    have e : (n-1)/n - 1 = -(1/n) := by field_simp; ring
    linarith
  have hnp : 0 < n := by linarith
  have hD : (n * logb 2 n)^2 = n^2 * log n^2 / log 2^2 := by
    rw [show logb 2 n = log n / log 2 from rfl]; field_simp
  have e2 : 1/log (n-1) - 1/log n = (log n - log (n-1))/(log (n-1) * log n) := by
    field_simp
  rw [hD, e2]
  have hDp : 0 < n^2 * log n^2 / log 2^2 := by positivity
  calc _ ≤ 2 * n / (n^2 * log n^2 / log 2^2) := div_le_div_of_nonneg_right hs hDp.le
    _ = 2 * log 2 ^2 * (1/n / (log n ^2)) := by field_simp
    _ ≤ 2 * log 2 ^2 * ((log n - log (n-1))/(log (n-1) * log n)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc 1/n / log n ^2 ≤ (log n - log (n-1)) / log n ^2 := by gcongr
          _ ≤ _ := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            nlinarith

noncomputable abbrev putnam_1982_a2_solution : Prop := True
theorem putnam_1982_a2
(B : ℕ → ℝ → ℝ)
(hB : B = fun (n : ℕ) (x : ℝ) ↦ ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ x)
(f : ℕ → ℝ)
(hf : f = fun n ↦ B n (logb n 2) / (n * logb 2 n) ^ 2)
: (∃ L : ℝ, Tendsto (fun N ↦ ∑ j ∈ Finset.Icc 2 N, f j) atTop (𝓝 L)) ↔ putnam_1982_a2_solution := by
  have hnn : ∀ n, 0 ≤ f n := by
    intro n; subst hf hB; simp only
    apply div_nonneg (Finset.sum_nonneg fun k _ => by positivity) (by positivity)
  have hle : ∀ m : ℕ, f (m+3) ≤ 2 * (log 2)^2 * (1/log ((m+2:ℕ):ℝ) - 1/log ((m+3:ℕ):ℝ)) := by
    intro m; subst hf hB; exact key m
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hbd : ∀ m : ℕ, ∑ i ∈ Finset.range (m+3), f i ≤ ∑ i ∈ Finset.range 3, f i + 2 * (log 2)^2 * (1/log 2 - 1/log ((m+2:ℕ):ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := hle m
      have e : m + 1 + 2 = m + 3 := by ring
      rw [e]
      nlinarith
  have hpos : 0 ≤ 2 * (log 2)^2 * (1/log 2) := by positivity
  have hsum : Summable f := by
    apply summable_of_sum_range_le hnn (c := ∑ i ∈ Finset.range 3, f i + 2 * (log 2)^2 * (1/log 2))
    intro N
    have h1 : ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range (N+3), f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => hnn i)
    have h2 : 0 ≤ 1/log ((N+2:ℕ):ℝ) := by
      have : 0 ≤ log ((N+2:ℕ):ℝ) := Real.log_nonneg (by push_cast; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)])
      positivity
    have := hbd N
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (log 2)^2) h2]
  have ht := hsum.hasSum.tendsto_sum_nat
  constructor
  · intro _; trivial
  · intro _
    refine ⟨∑' i, f i - (f 0 + f 1), ?_⟩
    have := (ht.comp (tendsto_add_atTop_nat 1)).sub_const (f 0 + f 1)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp]
    have : ∀ N, 1 ≤ N → ∑ i ∈ Finset.range (N+1), f i = f 0 + f 1 + ∑ j ∈ Finset.Icc 2 N, f j := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp [Finset.sum_range_succ]
      | succ k hk ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]; ring
    rw [this N hN]; ring
