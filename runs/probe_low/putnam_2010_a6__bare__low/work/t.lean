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
  have A : ∀ b : ℕ → ℝ, (∀ k, 0 < b k) → (∀ k, b (k+1) ≤ b k) → Tendsto b atTop (𝓝 0) →
      ∀ M : ℝ, ¬ ∀ n, ∑ k ∈ Finset.range n, (1 - b (k+1) / b k) ≤ M := by
    intro b hpos hanti hlim M hM
    have hd0 : ∀ k, 0 ≤ 1 - b (k+1) / b k := fun k => by
      have := (div_le_one (hpos k)).2 (hanti k)
      linarith
    have hsum : Summable (fun k => 1 - b (k+1) / b k) := summable_of_sum_range_le hd0 hM
    have hdt := hsum.tendsto_atTop_zero
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      (hdt.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)))
    have key : ∀ k ≥ K, Real.log (b k) - Real.log (b (k+1)) ≤ 2 * (1 - b (k+1) / b k) := by
      intro k hk
      have h1 := hK k hk
      have hp := hpos k
      have hq := hpos (k+1)
      have hqp := hanti k
      have h2 : b k ≤ 2 * b (k+1) := by
        have : 1/2 < b (k+1) / b k := by linarith
        rw [lt_div_iff₀ hp] at this
        linarith
      rw [← Real.log_div hp.ne' hq.ne']
      have h3 := Real.log_le_sub_one_of_pos (div_pos hp hq)
      have h4 : 0 ≤ (b k - b (k+1)) * (2 * b (k+1) - b k) :=
        mul_nonneg (by linarith) (by linarith)
      have h5 : b k / b (k+1) - 1 - 2 * (1 - b (k+1) / b k)
          = -((b k - b (k+1)) * (2 * b (k+1) - b k)) / (b k * b (k+1)) := by
        field_simp
        ring
      have h6 : 0 ≤ ((b k - b (k+1)) * (2 * b (k+1) - b k)) / (b k * b (k+1)) :=
        div_nonneg h4 (by positivity)
      have h7 : -((b k - b (k+1)) * (2 * b (k+1) - b k)) / (b k * b (k+1))
          = -(((b k - b (k+1)) * (2 * b (k+1) - b k)) / (b k * b (k+1))) := by ring
      linarith
    have hlow : ∀ n, Real.log (b K) - 2 * M ≤ Real.log (b (K+n)) := by
      intro n
      have e := Finset.sum_range_sub' (fun i => Real.log (b (K+i))) n
      have h1 : ∑ i ∈ Finset.range n, (Real.log (b (K+i)) - Real.log (b (K+(i+1))))
          ≤ ∑ i ∈ Finset.range n, 2 * (1 - b (K+i+1) / b (K+i)) :=
        Finset.sum_le_sum (fun i _ => key (K+i) (by omega))
      rw [← Finset.mul_sum] at h1
      have h2 := Finset.sum_range_add (fun k => 1 - b (k+1) / b k) K n
      have h3 : 0 ≤ ∑ k ∈ Finset.range K, (1 - b (k+1) / b k) :=
        Finset.sum_nonneg (fun k _ => hd0 k)
      have h4 := hM (K+n)
      rw [Nat.add_zero] at e
      linarith
    have hev := hlim.eventually (gt_mem_nhds (Real.exp_pos (Real.log (b K) - 2 * M)))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    have := hN (K+N) (by omega)
    have h := Real.log_lt_log (hpos _) this
    rw [Real.log_exp] at h
    linarith [hlow N, hlow (N)]
  rintro ⟨y, hy⟩
  obtain ⟨hanti, hcont, hlim⟩ := hf
  have hpos : ∀ x, 0 ≤ x → 0 < f x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have h1 : f (x+1) < f x := hanti (by simpa using hx) (by simp; linarith) (by linarith)
    have h2 : ∀ᶠ t in atTop, f t ≤ f (x+1) := by
      filter_upwards [eventually_ge_atTop (x+1)] with t ht
      exact hanti.antitoneOn (by simp; linarith) (by simp; linarith) ht
    have := le_of_tendsto hlim h2
    linarith
  set g : ℝ → ℝ := fun x => (f x - f (x+1)) / f x with hg
  have hgc : ContinuousOn g (Ici 0) := by
    apply ContinuousOn.div
    · exact hcont.sub (hcont.comp (continuousOn_id.add continuousOn_const)
        (fun x hx => by simp at hx ⊢; linarith))
    · exact hcont
    · intro x hx; exact (hpos x hx).ne'
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable g MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply hgc.mono
    intro x hx
    exact le_trans (le_min ha hb) hx.1
  have hF : ∀ z, 0 ≤ z → ∫ x in Ico 0 z, g x = ∫ x in (0:ℝ)..z, g x := by
    intro z hz
    rw [intervalIntegral.integral_of_le hz, MeasureTheory.integral_Ico_eq_integral_Ioc]
  set b : ℕ → ℝ := fun k => f (((k:ℝ)+1)/2) with hb
  have hbpos : ∀ k, 0 < b k := fun k => hpos _ (by positivity)
  have hbanti : ∀ k, b (k+1) ≤ b k := fun k => by
    apply hanti.antitoneOn
    · simp only [mem_Ici]; positivity
    · simp only [mem_Ici]; positivity
    · push_cast; linarith
  have hblim : Tendsto b atTop (𝓝 0) := by
    apply hlim.comp
    apply Tendsto.atTop_div_const (by norm_num)
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have step : ∀ n : ℕ, (1 - b (n+1) / b n) / 2 ≤ ∫ x in ((n:ℝ)/2)..(((n:ℝ)+1)/2), g x := by
    intro n
    have hn : (0:ℝ) ≤ (n:ℝ)/2 := by positivity
    have := intervalIntegral.integral_mono_on (a := (n:ℝ)/2) (b := ((n:ℝ)+1)/2)
      (by linarith) (intervalIntegrable_const (c := (1 - b (n+1) / b n)))
      (hint _ _ hn (by positivity)) (g := g) (f := fun _ => 1 - b (n+1) / b n) (by
        intro x hx
        have hx0 : 0 ≤ x := le_trans hn hx.1
        have h1 := hpos x hx0
        have h2 := hpos (((n:ℝ)+1)/2) (by positivity)
        have h3 : f (x+1) ≤ f (((n:ℝ)+2)/2) :=
          hanti.antitoneOn (by simp only [mem_Ici]; positivity) (by simp only [mem_Ici]; linarith)
            (by linarith [hx.1])
        have h4 : f (((n:ℝ)+1)/2) ≤ f x :=
          hanti.antitoneOn (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith)
            hx.2
        have h5 : b (n+1) = f (((n:ℝ)+2)/2) := by
          simp only [hb]; push_cast; ring_nf
        have h6 : b n = f (((n:ℝ)+1)/2) := rfl
        have h7 := hpos (x+1) (by linarith)
        have h8 : f (x+1) / f x ≤ b (n+1) / b n := by
          rw [h5, h6]
          exact div_le_div₀ (hpos _ (by positivity)).le h3 h2 h4
        show _ ≤ (f x - f (x+1)) / f x
        rw [sub_div, div_self h1.ne']
        linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e2 : ((n:ℝ)+1)/2 - (n:ℝ)/2 = 1/2 := by ring
    rw [e2] at this
    linarith
  have hsumle : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 - b (k+1) / b k)
      ≤ 2 * ∫ x in (0:ℝ)..((n:ℝ)/2), g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := intervalIntegral.integral_add_adjacent_intervals
        (hint 0 ((n:ℝ)/2) le_rfl (by positivity))
        (hint ((n:ℝ)/2) (((n:ℝ)+1)/2) (by positivity) (by positivity))
      have e : (((n+1:ℕ):ℝ))/2 = ((n:ℝ)+1)/2 := by push_cast; ring
      rw [e, ← this]
      linarith [step n]
  have hev := (hy.comp (Tendsto.atTop_div_const (r := (2:ℝ)) (by norm_num)
    tendsto_natCast_atTop_atTop)).eventually (gt_mem_nhds (show y < y + 1 by linarith))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hbound : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 - b (k+1) / b k) ≤ 2 * (y+1) := by
    intro n
    have h1 := hN (max n N) (le_max_right _ _)
    simp only [Function.comp] at h1
    rw [hF _ (by positivity)] at h1
    have h2 : ∑ k ∈ Finset.range n, (1 - b (k+1) / b k)
        ≤ ∑ k ∈ Finset.range (max n N), (1 - b (k+1) / b k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
        (fun k _ _ => by
          have := (div_le_one (hbpos k)).2 (hbanti k)
          linarith)
    linarith [hsumle (max n N)]
  exact A b hbpos hbanti hblim _ hbound
