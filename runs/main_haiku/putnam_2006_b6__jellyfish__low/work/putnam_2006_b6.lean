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
  have hK : (1:ℝ) < k := by exact_mod_cast hk
  have hKpos : (0:ℝ) < k := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 + 1/(k:ℝ) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    have : 0 < 1/(k:ℝ) := by positivity
    rw [hp]; linarith
  have hp0 : 0 < p := by linarith
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have : 0 < 1/(a m)^((1:ℝ)/k) := one_div_pos.mpr (Real.rpow_pos_of_pos ih _)
      linarith
  have hxp : ∀ x : ℝ, 0 < x → x^p = x * x^((1:ℝ)/k) := by
    intro x hx
    rw [hp, Real.rpow_add hx, Real.rpow_one]
  have hsx : ∀ x : ℝ, 0 < x → 0 < x^((1:ℝ)/k) := fun x hx => Real.rpow_pos_of_pos hx _
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = (a n)^p := ⟨fun n => (a n)^p, fun n => rfl⟩
  have key_lower : ∀ n, u n + p ≤ u (n+1) := by
    intro n
    have hx := hpos n
    have hsxpos := hsx _ hx
    rw [hu_def, hu_def, hxp _ hx, ha n]
    have hh : 0 ≤ 1/(a n)^((1:ℝ)/k) := by positivity
    have hq : 0 ≤ 1/(a n)^((1:ℝ)/k) / a n := by positivity
    have hbern := one_add_mul_self_le_rpow_one_add (s := 1/(a n)^((1:ℝ)/k)/a n) (by linarith) hp1
    have hrel : 1 + 1/(a n)^((1:ℝ)/k)/a n = (a n + 1/(a n)^((1:ℝ)/k))/a n := by
      field_simp
    rw [hrel, Real.div_rpow (by linarith) hx.le, le_div_iff₀ (Real.rpow_pos_of_pos hx _), hxp _ hx] at hbern
    have e1 : 1/(a n)^((1:ℝ)/k)/a n * (a n * (a n)^((1:ℝ)/k)) = 1 := by
      field_simp
    have e2 : (1 + p*(1/(a n)^((1:ℝ)/k)/a n)) * (a n * (a n)^((1:ℝ)/k)) = a n * (a n)^((1:ℝ)/k) + p := by
      linear_combination p * e1
    linarith
  have key_upper : ∀ n, u (n+1) - u n ≤ p * (1 + 1/u n)^((1:ℝ)/k) := by
    intro n
    have hx := hpos n
    have hy := hpos (n+1)
    have hsxpos := hsx _ hx
    have hyeq : a (n+1) = a n + 1/(a n)^((1:ℝ)/k) := ha n
    have hr : 1 + 1/u n = a (n+1) / a n := by
      rw [hu_def, hxp _ hx, hyeq]
      field_simp
    rw [hr, Real.div_rpow hy.le hx.le, hu_def, hu_def, hxp _ hy, hxp _ hx]
    have hty := hsx _ hy
    have hh : 0 < 1/(a n)^((1:ℝ)/k) := one_div_pos.mpr hsxpos
    have hle : 1/(a n)^((1:ℝ)/k) / a (n+1) ≤ 1 := by
      rw [div_le_one hy]; rw [hyeq] at *; linarith
    have hbern := one_add_mul_self_le_rpow_one_add (s := -(1/(a n)^((1:ℝ)/k) / a (n+1))) (by linarith) hp1
    have hrel : 1 + -(1/(a n)^((1:ℝ)/k) / a (n+1)) = a n / a (n+1) := by
      rw [hyeq]; field_simp; ring
    rw [hrel, Real.div_rpow hx.le hy.le, le_div_iff₀ (Real.rpow_pos_of_pos hy _), hxp _ hy] at hbern
    have e3 : (1 + p*(-(1/(a n)^((1:ℝ)/k) / a (n+1)))) * (a (n+1) * a (n+1)^((1:ℝ)/k))
        = a (n+1) * a (n+1)^((1:ℝ)/k) - p * a (n+1)^((1:ℝ)/k) * (1/(a n)^((1:ℝ)/k)) := by
      field_simp
      ring
    have e4 : p * (a (n+1)^((1:ℝ)/k) / (a n)^((1:ℝ)/k)) = p * a (n+1)^((1:ℝ)/k) * (1/(a n)^((1:ℝ)/k)) := by
      ring
    rw [e4, hxp _ hx] at *
    linarith
  have hu_tend : Filter.Tendsto u Filter.atTop Filter.atTop := by
    have hlow : ∀ n : ℕ, u 0 + p * (n:ℝ) ≤ u n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => push_cast; linarith [key_lower m]
    exact Filter.tendsto_atTop_mono hlow
      (Filter.tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hp0))
  have hinv : Filter.Tendsto (fun n => 1/u n) Filter.atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hu_tend
  have hg : Filter.Tendsto (fun n => p * (1 + 1/u n)^((1:ℝ)/k)) Filter.atTop (nhds p) := by
    have h1 : Filter.Tendsto (fun n => 1 + 1/u n) Filter.atTop (nhds 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).add hinv
      simpa using this
    have h2 := ((h1.rpow_const (p := (1:ℝ)/k) (Or.inr (by positivity))).const_mul p)
    simpa using h2
  have hd : Filter.Tendsto (fun n => u (n+1) - u n) Filter.atTop (nhds p) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Filter.Eventually.of_forall fun n => by linarith [key_lower n])
      (Filter.Eventually.of_forall fun n => key_upper n)
  have hces := hd.cesaro
  have hC : Filter.Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, (u (i+1) - u i)) + u 0 / (n:ℝ))
      Filter.atTop (nhds (p + 0)) :=
    hces.add (tendsto_const_div_atTop_nhds_zero_nat (u 0))
  rw [add_zero] at hC
  have hD : (fun n : ℕ => u n / (n:ℝ)) = fun n : ℕ => (n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, (u (i+1) - u i)) + u 0 / (n:ℝ) := by
    funext n
    rw [Finset.sum_range_sub]
    ring
  have hlim : Filter.Tendsto (fun n : ℕ => u n / (n:ℝ)) Filter.atTop (nhds p) := by
    rw [hD]; exact hC
  have hE : ∀ n : ℕ, (a n)^(k+1)/((n:ℝ)^k) = (u n / (n:ℝ))^k := by
    intro n
    have hcast : p * (k:ℝ) = ((k+1 : ℕ) : ℝ) := by
      rw [hp]; push_cast; field_simp
    have hpow : (a n ^ p)^k = a n ^ (k+1) := by
      rw [← Real.rpow_natCast (a n ^ p) k, ← Real.rpow_mul (hpos n).le, hcast, Real.rpow_natCast]
    rw [div_pow, hu_def, hpow]
  have hp_eq : p^k = putnam_2006_b6_solution k := by
    simp only [putnam_2006_b6_solution]
    rw [hp]
    congr 1
    field_simp
  have := hlim.pow k
  rw [hp_eq] at this
  exact this.congr (fun n => (hE n).symm)
