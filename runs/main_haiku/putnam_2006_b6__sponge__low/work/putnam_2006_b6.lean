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
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1:ℝ)/k := ⟨_, rfl⟩
  rw [← hq] at ha
  have hkR : (1:ℝ) < k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hqk : q * (k:ℝ) = 1 := by rw [hq]; field_simp
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqpos : ∀ u : ℝ, 0 < u → 0 < u ^ q := fun u hu => Real.rpow_pos_of_pos hu q
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have h1 := hqpos _ ih
      have h2 : 0 < 1 / (a m)^q := by positivity
      linarith
  have hmono : ∀ n, a n ≤ a (n+1) := by
    intro n
    rw [ha n]
    have h1 := hqpos _ (hpos n)
    have h2 : 0 < 1 / (a n)^q := by positivity
    linarith
  have hpowq : ∀ u : ℝ, 0 < u → (u ^ q) ^ k = u := by
    intro u hu
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le, hqk, Real.rpow_one]
  have hpow1 : ∀ u v : ℝ, 0 < u → 0 < v → (v/u)^(1+q) = (v/u) * (v^q / u^q) := by
    intro u v hu hv
    rw [Real.rpow_add (div_pos hv hu), Real.rpow_one, Real.div_rpow hv.le hu.le]
  have hbern : ∀ r : ℝ, 0 < r → 1 + (1+q)*(r-1) ≤ r^(1+q) := by
    intro r _
    have h := one_add_mul_self_le_rpow_one_add (s := r-1) (by linarith) (p := 1+q) (by linarith)
    have h2 : (1:ℝ) + (r-1) = r := by ring
    rw [h2] at h
    exact h
  have hL : ∀ u v U V : ℝ, 0 < u → 0 < U → 0 < v → 0 < V → v - u = 1/U →
      1 + (1+q)*(v/u-1) ≤ (v/u)*(V/U) → (1+q) ≤ v*V - u*U := by
    intro u v U V hu hU hv hV hvu h
    have h1 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ u*U)
    have h2 : (v/u)*(V/U)*(u*U) = v*V := by field_simp
    have h3 : (1 + (1+q)*(v/u-1)) * (u*U) = u*U + (1+q)*((v-u)*U) := by
      field_simp
    have h4 : (v-u)*U = 1 := by rw [hvu]; field_simp
    rw [h2, h3, h4] at h1
    linarith
  have hW : ∀ u v U V : ℝ, 0 < u → 0 < U → 0 < v → 0 < V → U^k = u → V^k = v → u ≤ v →
      V/U ≤ v/u := by
    intro u v U V hu hU hv hV hUk hVk huv
    have hwk : (V/U)^k = v/u := by rw [div_pow, hVk, hUk]
    rcases le_total (V/U) 1 with h | h
    · have : 1 ≤ v/u := (one_le_div hu).mpr huv
      linarith
    · have := le_self_pow₀ h (by omega : k ≠ 0)
      rw [hwk] at this
      exact this
  have hU' : ∀ u v U V : ℝ, 0 < u → 0 < U → 0 < v → 0 < V → v - u = 1/U → u ≤ v →
      U^k = u → V^k = v →
      1 + (1+q)*(u/v-1) ≤ (u/v)*(U/V) → v*V - u*U ≤ (1+q)*(v/u) := by
    intro u v U V hu hU hv hV hvu huv hUk hVk h
    have hw := hW u v U V hu hU hv hV hUk hVk huv
    have h1 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ v*V)
    have h2 : (u/v)*(U/V)*(v*V) = u*U := by field_simp
    have h3 : (1 + (1+q)*(u/v-1)) * (v*V) = v*V + (1+q)*((u-v)*V) := by
      field_simp
    have h4 : (u-v)*V = -(V/U) := by
      have : u - v = -(1/U) := by linarith
      rw [this]; ring
    rw [h2, h3, h4] at h1
    have h5 : (1+q)*(V/U) ≤ (1+q)*(v/u) := mul_le_mul_of_nonneg_left hw (by linarith)
    nlinarith
  have hvu : ∀ n, a (n+1) - a n = 1 / (a n)^q := by
    intro n; rw [ha n]; ring
  have hstep_lo : ∀ n, (1+q) ≤ (a (n+1) * a (n+1)^q) - (a n * a n ^ q) := by
    intro n
    refine hL _ _ _ _ (hpos n) (hqpos _ (hpos n)) (hpos (n+1)) (hqpos _ (hpos (n+1)))
      (hvu n) ?_
    have := hbern _ (div_pos (hpos (n+1)) (hpos n))
    rw [hpow1 _ _ (hpos n) (hpos (n+1))] at this
    exact this
  have hstep_hi : ∀ n, (a (n+1) * a (n+1)^q) - (a n * a n ^ q) ≤ (1+q) * (a (n+1) / a n) := by
    intro n
    refine hU' _ _ _ _ (hpos n) (hqpos _ (hpos n)) (hpos (n+1)) (hqpos _ (hpos (n+1)))
      (hvu n) (hmono n) (hpowq _ (hpos n)) (hpowq _ (hpos (n+1))) ?_
    have := hbern _ (div_pos (hpos n) (hpos (n+1)))
    rw [hpow1 _ _ (hpos (n+1)) (hpos n)] at this
    exact this
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ n, x n = a n * a n ^ q := ⟨_, fun n => rfl⟩
  have hxlo : ∀ n : ℕ, (n:ℝ) * (1+q) ≤ x n := by
    intro n
    rw [hx]
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul]; exact (mul_pos (hpos 0) (hqpos _ (hpos 0))).le
    | succ m ih =>
      have := hstep_lo m
      push_cast
      linarith
  have hxk : ∀ n, (x n)^k = (a n)^(k+1) := by
    intro n
    rw [hx, mul_pow, hpowq _ (hpos n), pow_succ]
  have hainf : Tendsto a atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨⌈max b 0 ^ (k+1)⌉₊ + 1, fun n hn => ?_⟩
    have hn1 : (1:ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hbase : (n:ℝ) * (1+q) ≤ x n := hxlo n
    have hb1 : (n:ℝ) ≤ (x n)^k := by
      have h1 : (n:ℝ) ≤ (n:ℝ) * (1+q) := by nlinarith
      have h4 : (n:ℝ) ≤ (x n) := le_trans h1 hbase
      have h5 : (x n) ≤ (x n)^k := by
        have hxn1 : (1:ℝ) ≤ x n := le_trans hn1 h4
        exact le_self_pow₀ hxn1 (by omega : k ≠ 0)
      exact le_trans h4 h5
    rw [hxk] at hb1
    have hcast : (⌈max b 0 ^ (k+1)⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hc : max b 0 ^ (k+1) ≤ (⌈max b 0 ^ (k+1)⌉₊ : ℝ) := Nat.le_ceil _
    by_contra hcon
    have hlt : a n < max b 0 := lt_of_lt_of_le (not_le.mp hcon) (le_max_left _ _)
    have := pow_lt_pow_left₀ hlt (hpos n).le (by omega : k+1 ≠ 0)
    linarith
  have hratio : Tendsto (fun n => a (n+1) / a n) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n => 1 / a n) atTop (𝓝 0) := by
      have h : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hainf
      simpa [one_div] using h
    have hup : Tendsto (fun n => 1 + 1 / a n) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).add hinv
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Eventually.of_forall (fun n => (one_le_div (hpos n)).mpr (hmono n))
    · filter_upwards [hainf.eventually_ge_atTop 1] with n hn
      have hU1 : (1:ℝ) ≤ (a n)^q := Real.one_le_rpow hn (by linarith)
      have ht : 1 / (a n)^q ≤ 1 := by
        rw [div_le_one (hqpos _ (hpos n))]; exact hU1
      rw [div_le_iff₀ (hpos n), ha n]
      have e : (1 + 1 / a n) * a n = a n + 1 := by
        field_simp
      rw [e]
      linarith
  have he : Tendsto (fun n => x (n+1) - x n) atTop (𝓝 (1+q)) := by
    have hl : ∀ n, (1+q) ≤ x (n+1) - x n := fun n => by rw [hx, hx]; exact hstep_lo n
    have hh : ∀ n, x (n+1) - x n ≤ (1+q) * (a (n+1) / a n) := fun n => by
      rw [hx, hx]; exact hstep_hi n
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    · simpa using hratio.const_mul (1+q)
    · exact Eventually.of_forall hl
    · exact Eventually.of_forall hh
  have hces := he.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (x (i+1) - x i) = x n - x 0 :=
    fun n => Finset.sum_range_sub x n
  have hces2 : Tendsto (fun n:ℕ => (n:ℝ)⁻¹ * (x n - x 0)) atTop (𝓝 (1+q)) :=
    hces.congr (fun n => by simp only [hsum])
  have h0 : Tendsto (fun n:ℕ => x 0 * (n:ℝ)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (x 0)
    simpa using this
  have hratio2 : Tendsto (fun n:ℕ => x n / n) atTop (𝓝 (1+q)) := by
    have := hces2.add h0
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    try dsimp only
    ring
  have hfin := hratio2.pow k
  have hsol : putnam_2006_b6_solution k = (1+q)^k := by
    simp only [putnam_2006_b6_solution]
    rw [hq]
    congr 1
    field_simp
  rw [hsol]
  apply hfin.congr'
  filter_upwards with n
  rw [div_pow, hxk n]
