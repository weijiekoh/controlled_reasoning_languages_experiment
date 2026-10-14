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
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (putnam_2006_b6_solution k)) :=
by
  have hkR : (1:ℝ) < k := by exact_mod_cast hk
  have hk0 : (k:ℝ) ≠ 0 := ne_of_gt (by linarith)
  set p : ℝ := ((k:ℝ)+1)/k with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have := Real.rpow_pos_of_pos ih ((1:ℝ)/k)
      positivity
  have hstep : ∀ n, 0 < 1/((a n)^((1 : ℝ)/k)) := fun n => by
    have := Real.rpow_pos_of_pos (hpos n) ((1:ℝ)/k)
    positivity
  have hmono : Monotone a :=
    monotone_nat_of_le_succ (fun n => by rw [ha n]; linarith [hstep n])
  have hunb : ∀ b : ℝ, ∃ n, b ≤ a n := by
    intro b
    by_contra hcon
    push_neg at hcon
    have hb : 0 < b := lt_trans (hpos 0) (hcon 0)
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 1 / b^((1:ℝ)/k) := ⟨_, rfl⟩
    have hc : 0 < c := by
      have := Real.rpow_pos_of_pos hb ((1:ℝ)/k)
      rw [hc_def]; positivity
    have hinc : ∀ n, c ≤ 1/((a n)^((1 : ℝ)/k)) := by
      intro n
      rw [hc_def]
      apply one_div_le_one_div_of_le
      · exact Real.rpow_pos_of_pos (hpos n) _
      · exact Real.rpow_le_rpow (le_of_lt (hpos n)) (le_of_lt (hcon n)) (by positivity)
    have hlow : ∀ n : ℕ, a 0 + n * c ≤ a n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [ha m]; push_cast
        linarith [hinc m]
    obtain ⟨n, hn⟩ := exists_nat_gt (b / c)
    have h1 : b < n * c := by rwa [div_lt_iff₀ hc] at hn
    have h2 := hlow n
    linarith [hcon n, ha0]
  have htop : Tendsto a atTop atTop := tendsto_atTop_atTop_of_monotone hmono hunb
  have hεlim : Tendsto (fun n => (a n)^(-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp0).comp htop
  have hεpos : ∀ n, 0 < (a n)^(-p) := fun n => Real.rpow_pos_of_pos (hpos n) _
  have hkey : ∀ n, (a n)^(-p) * a n = 1 / (a n)^((1:ℝ)/k) := by
    intro n
    have e : -p + 1 = -((1:ℝ)/k) := by rw [hp]; field_simp; ring
    rw [← Real.rpow_add_one (ne_of_gt (hpos n)), e, Real.rpow_neg (le_of_lt (hpos n))]
    exact inv_eq_one_div _
  have hrec : ∀ n, a (n+1) = a n * (1 + (a n)^(-p)) := by
    intro n
    have := hkey n
    rw [ha n]
    linear_combination (-1:ℝ) * this
  have hz : ∀ n, (a (n+1))^p = (a n)^p * (1 + (a n)^(-p))^p := by
    intro n
    rw [hrec n, Real.mul_rpow (le_of_lt (hpos n)) (by linarith [hεpos n])]
  have hzε : ∀ n, (a n)^p * (a n)^(-p) = 1 := by
    intro n
    rw [← Real.rpow_add (hpos n)]; simp
  have hzinv : ∀ n, (a n)^p = ((a n)^(-p))⁻¹ := fun n => eq_inv_of_mul_eq_one_left (hzε n)
  have hd : ∀ n, (a (n+1))^p - (a n)^p = ((a n)^(-p))⁻¹ * ((1 + (a n)^(-p))^p - 1) := by
    intro n
    rw [hz n, hzinv n]; ring
  have h : HasDerivAt (fun x : ℝ => x^p) p 1 := by
    simpa using Real.hasDerivAt_rpow_const (p := p) (x := 1) (Or.inl one_ne_zero)
  have hslope0 : Tendsto (fun t : ℝ => t⁻¹ * ((1+t)^p - 1)) (𝓝[≠] 0) (𝓝 p) := by
    have h2 := hasDerivAt_iff_tendsto_slope_zero.1 h
    simpa [smul_eq_mul, Real.one_rpow] using h2
  have hslope : Tendsto (fun n => ((a n)^(-p))⁻¹ * ((1 + (a n)^(-p))^p - 1)) atTop (𝓝 p) :=
    hslope0.comp (tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall fun n => (hεpos n).ne'⟩)
  have hdlim : Tendsto (fun n => (a (n+1))^p - (a n)^p) atTop (𝓝 p) := by
    simp only [hd]; exact hslope
  have hces := hdlim.cesaro
  have htel : ∀ n, ∑ i ∈ Finset.range n, ((a (i+1))^p - (a i)^p) = (a n)^p - (a 0)^p :=
    fun n => Finset.sum_range_sub (fun i => (a i)^p) n
  simp only [htel] at hces
  have hz0 : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * (a 0)^p) atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.mul_const ((a 0)^p)
  have hsum := hces.add hz0
  rw [add_zero] at hsum
  have hfin : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * (a n)^p) atTop (𝓝 p) :=
    Tendsto.congr (fun n => by ring) hsum
  have hfinal := hfin.pow k
  have hsol : putnam_2006_b6_solution k = p^k := rfl
  rw [hsol]
  refine hfinal.congr (fun n => ?_)
  have hpk : ((a n)^p)^k = (a n)^(k+1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hpos n)), ← Real.rpow_natCast]
    congr 1
    push_cast
    rw [hp]; field_simp
  rw [mul_pow, hpk, inv_pow]
  ring
