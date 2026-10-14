import Mathlib

open Filter Topology Set

-- Note: uses (ℝ → ℝ) instead of (Ici 0 → ℝ)
/--
Let $f:[0,\infty)\to \mathbb{R}$ be a strictly decreasing continuous function
such that $\lim_{x\to\infty} f(x) = 0$. Prove that
$\int_0^\infty \frac{f(x)-f(x+1)}{f(x)}\,dx$ diverges.
-/
theorem putnam_2010_a6
(f : ℝ → ℝ)
(hf : (StrictAntiOn f (Ici 0) ∧ ContinuousOn f (Ici 0) ∧ Tendsto f atTop (𝓝 0)))
: ¬∃ y : ℝ, Tendsto (fun z : ℝ => ∫ x in Ico 0 z, ((f x) - f (x + 1))/(f x)) atTop (𝓝 y) :=
by
  obtain ⟨hanti, hcont, hlim⟩ := hf
  have hpos : ∀ x, 0 ≤ x → 0 < f x := by
    intro x hx
    have h1 : 0 ≤ f (x+1) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop (x+1)] with t ht
      exact hanti.antitoneOn (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith) ht
    have := hanti (show x ∈ Ici (0:ℝ) from hx) (show x+1 ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith) (by linarith)
    linarith
  set g : ℝ → ℝ := fun x => ((f x) - f (x + 1))/(f x) with hg
  have hg0 : ∀ x, 0 ≤ x → 0 ≤ g x := by
    intro x hx
    have := hanti (show x ∈ Ici (0:ℝ) from hx) (show x+1 ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith) (by linarith)
    exact div_nonneg (by linarith) (hpos x hx).le
  have hgc : ContinuousOn g (Ici 0) := by
    apply ContinuousOn.div
    · exact hcont.sub (hcont.comp (continuousOn_id.add continuousOn_const) (fun x hx => by simp only [mem_Ici] at hx ⊢; linarith))
    · exact hcont
    · intro x hx; exact (hpos x hx).ne'
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable g MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply hgc.mono
    intro t ht
    have h2 : min a b ≤ t := ht.1
    simp only [mem_Ici]
    have : 0 ≤ min a b := le_min ha hb
    linarith
  rintro ⟨y, hy⟩
  set S : ℕ → ℝ → ℝ := fun n x => ∑ k ∈ Finset.range n, g (x + k) with hS
  have hSint : ∀ k : ℕ, IntervalIntegrable (fun x => g (x + k)) MeasureTheory.volume 0 1 := by
    intro k
    have := (hint (0+k) (1+k) (by positivity) (by positivity)).comp_add_right (k:ℝ)
    simpa using this
  have hSi : ∀ n, IntervalIntegrable (S n) MeasureTheory.volume 0 1 :=
    fun n => by
      have e : S n = ∑ i ∈ Finset.range n, fun x => g (x + i) := by
        funext x; simp [hS]
      rw [e]
      exact IntervalIntegrable.sum (Finset.range n) (fun k _ => hSint k)
  have hG : ∀ n : ℕ, ∫ x in Ico 0 (n:ℝ), g x = ∫ x in (0:ℝ)..1, S n x := by
    intro n
    have e1 : ∫ x in Ico 0 (n:ℝ), g x = ∫ x in (0:ℝ)..n, g x := by
      rw [intervalIntegral.integral_of_le (by positivity), MeasureTheory.integral_Ico_eq_integral_Ioo,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [e1]
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
      (a := fun k : ℕ => (k:ℝ)) (n := n) (fun k _ => hint _ _ (by positivity) (by positivity))
    simp only [Nat.cast_zero] at this
    rw [← this]
    simp only [hS]
    rw [intervalIntegral.integral_finset_sum (fun k _ => hSint k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_comp_add_right (fun x => g x)]
    simp [add_comm]
  have hIk : ∀ k : ℕ, 0 ≤ ∫ x in (0:ℝ)..1, g (x + k) := by
    intro k
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact hg0 _ (by have := hx.1; positivity)
  have hbound : ∀ n : ℕ, ∫ x in (0:ℝ)..1, S n x ≤ y := by
    intro n
    have hmono : ∀ m, n ≤ m → ∫ x in (0:ℝ)..1, S n x ≤ ∫ x in (0:ℝ)..1, S m x := by
      intro m hm
      apply intervalIntegral.integral_mono_on (by norm_num) (hSi n) (hSi m)
      intro x hx
      simp only [hS]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      intro k _ _
      exact hg0 _ (by have := hx.1; positivity)
    have ht : Tendsto (fun m : ℕ => ∫ x in (0:ℝ)..1, S m x) atTop (𝓝 y) := by
      simp_rw [← hG]
      exact hy.comp tendsto_natCast_atTop_atTop
    exact ge_of_tendsto ht (eventually_atTop.2 ⟨n, hmono⟩)
  have hSnn : ∀ n, ∀ x, 0 ≤ x → 0 ≤ S n x := by
    intro n x hx
    exact Finset.sum_nonneg (fun k _ => hg0 _ (by positivity))
  have hpt : ∀ x ∈ Ioc (0:ℝ) 1, Tendsto (fun n => S n x) atTop atTop := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    have hmon : Monotone (fun n => S n x) := by
      apply monotone_nat_of_le_succ
      intro n
      simp only [hS]
      rw [Finset.sum_range_succ]
      have := hg0 (x + n) (by positivity)
      linarith
    apply tendsto_atTop_atTop_of_monotone hmon
    intro B
    by_contra hcon
    push_neg at hcon
    have hB : ∀ n, S n x ≤ B := fun n => (hcon n).le
    have hsum : Summable (fun k : ℕ => g (x + k)) :=
      summable_of_sum_range_le (fun k => hg0 _ (by positivity)) hB
    have hz := hsum.tendsto_atTop_zero
    obtain ⟨K, hK⟩ := (eventually_atTop.1 (hz.eventually (ge_mem_nhds (show (0:ℝ) < 1/2 by norm_num))))
    set L : ℕ → ℝ := fun k => Real.log (f (x+k)) - Real.log (f (x+k+1)) with hL
    set h : ℕ → ℝ := fun k => if k < K then |L k| else 0 with hh
    have hhs : Summable h := summable_of_ne_finset_zero (s := Finset.range K) (by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [hh, not_lt.2 hk])
    have hLle : ∀ k, L k ≤ 2 * g (x + k) + h k := by
      intro k
      have hfk := hpos (x+k) (by positivity)
      have hfk1 := hpos (x+k+1) (by positivity)
      have hgk := hg0 (x+k) (by positivity)
      by_cases hk : k < K
      · simp only [hh, hk, if_true]
        have := le_abs_self (L k)
        linarith
      · simp only [hh, hk, if_false]
        have h1 := hK k (not_lt.1 hk)
        have h2 : g (x+k) = (f (x+k) - f (x+k+1)) / f (x+k) := rfl
        rw [h2] at h1 ⊢
        rw [div_le_iff₀ hfk] at h1
        have h3 : L k ≤ f (x+k) / f (x+k+1) - 1 := by
          have := Real.log_le_sub_one_of_pos (div_pos hfk hfk1)
          rwa [Real.log_div hfk.ne' hfk1.ne'] at this
        have h4 : f (x+k) / f (x+k+1) - 1 = (f (x+k) - f (x+k+1)) / f (x+k+1) := by
          field_simp
        have h5 : (f (x+k) - f (x+k+1)) / f (x+k+1) ≤ 2 * ((f (x+k) - f (x+k+1)) / f (x+k)) + 0 := by
          rw [add_zero, div_le_iff₀ hfk1, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hfk]
          have hnn : 0 ≤ f (x+k) - f (x+k+1) := by
            have := hgk
            have h2' : g (x+k) = (f (x+k) - f (x+k+1)) / f (x+k) := rfl
            rw [h2'] at this
            exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2, hfk])
          nlinarith
        linarith
    have hsum2 : Summable (fun k : ℕ => 2 * g (x + k) + h k) := (hsum.mul_left 2).add hhs
    set T := ∑' k : ℕ, (2 * g (x + k) + h k)
    have hbd : ∀ n : ℕ, Real.log (f x) - Real.log (f (x+n)) ≤ T := by
      intro n
      have e : ∑ k ∈ Finset.range n, L k = Real.log (f x) - Real.log (f (x+n)) := by
        have := Finset.sum_range_sub' (fun k : ℕ => Real.log (f (x+k))) n
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
        rw [← this]
        apply Finset.sum_congr rfl
        intro k _
        simp only [hL, add_assoc]
      rw [← e]
      calc ∑ k ∈ Finset.range n, L k ≤ ∑ k ∈ Finset.range n, (2 * g (x + k) + h k) :=
            Finset.sum_le_sum (fun k _ => hLle k)
        _ ≤ T := Summable.sum_le_tsum _ (fun (k:ℕ) _ => by
            have h0 := hg0 (x+k) (by positivity)
            have : 0 ≤ h k := by simp only [hh]; split_ifs <;> positivity
            positivity) hsum2
    have hf1 : Tendsto (fun n : ℕ => f (x+n)) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hlim.comp ?_, Eventually.of_forall (fun n => hpos _ (by positivity))⟩
      exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have hf2 := Real.tendsto_log_nhdsGT_zero.comp hf1
    have hf3 : Tendsto (fun n : ℕ => Real.log (f x) - Real.log (f (x+n))) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp hf2)
    obtain ⟨n, hn⟩ := (tendsto_atTop.1 hf3 (T+1)).exists
    have := hbd n
    linarith
  have hSI : ∀ n, MeasureTheory.IntegrableOn (S n) (Ioc 0 1) :=
    fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (hSi n)
  have hl : ∀ n, ∫⁻ x in Ioc (0:ℝ) 1, ENNReal.ofReal (S n x) ≤ ENNReal.ofReal y := by
    intro n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hSI n)
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall (fun x hx => hSnn n x hx.1.le)))]
    apply ENNReal.ofReal_le_ofReal
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact hbound n
  have hT := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (μ := MeasureTheory.volume.restrict (Ioc (0:ℝ) 1))
    (f := fun n x => ENNReal.ofReal (S n x)) (F := fun _ => ⊤)
    (fun n => (hSI n).aemeasurable.ennreal_ofReal)
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (fun x hx => by
      intro a b hab
      apply ENNReal.ofReal_le_ofReal
      simp only [hS]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      intro k _ _
      exact hg0 _ (by have := hx.1; positivity))))
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (fun x hx =>
      ENNReal.tendsto_ofReal_atTop.comp (hpt x hx))))
  have hfin : (∫⁻ x in Ioc (0:ℝ) 1, (⊤ : ENNReal)) ≤ ENNReal.ofReal y :=
    le_of_tendsto hT (Eventually.of_forall hl)
  simp at hfin
