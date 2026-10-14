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
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((k:ℝ)+1)/k := ⟨_, rfl⟩
  have hp1 : 1 + 1/(k:ℝ) = p := by rw [hp]; field_simp
  have hq0 : 0 ≤ 1/(k:ℝ) := by positivity
  have hq1 : 1/(k:ℝ) ≤ 1 := by rw [div_le_one hkpos]; linarith
  have hp_lo : 1 ≤ p := by linarith
  have hp_hi : p ≤ 2 := by linarith
  have apos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha n]
      have h1 : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos ih _
      have h2 := one_div_pos.mpr h1
      linarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ n, c n = (a n)^p := ⟨_, fun _ => rfl⟩
  have cpos : ∀ n, 0 < c n := fun n => by rw [hc n]; exact Real.rpow_pos_of_pos (apos n) _
  have hx : ∀ n, 0 < 1/c n := fun n => one_div_pos.mpr (cpos n)
  have hkey : ∀ n, a n * (1/c n) = 1/(a n)^((1:ℝ)/k) := by
    intro n
    have hcn : c n = a n * (a n)^((1:ℝ)/k) := by
      rw [hc n, ← hp1, Real.rpow_add (apos n), Real.rpow_one]
    have := Real.rpow_pos_of_pos (apos n) ((1:ℝ)/k)
    rw [hcn]
    have hne := (apos n).ne'
    field_simp
  have arec : ∀ n, a (n+1) = a n * (1 + 1/c n) := by
    intro n
    rw [ha n, ← hkey n]; ring
  have crec : ∀ n, c (n+1) = c n * (1 + 1/c n)^p := by
    intro n
    rw [hc (n+1), arec n, Real.mul_rpow (apos n).le (by linarith [hx n]), ← hc n]
  have bound : ∀ x : ℝ, 0 ≤ x → (1+x)^p ≤ 1 + p*x + x^2 := by
    intro x hx0
    have hsplit : (1+x)^p = (1+x)^(1:ℝ) * (1+x)^(p-1) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < 1+x)]
      congr 1; ring
    have h3 := rpow_one_add_le_one_add_mul_self (s := x) (by linarith) (p := p-1) (by linarith) (by linarith)
    rw [hsplit, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 1+x),
      mul_le_mul_of_nonneg_right (by linarith : p - 1 ≤ 1) (sq_nonneg x)]
  have hlow : ∀ n, p ≤ c (n+1) - c n := by
    intro n
    have h1 := one_add_mul_self_le_rpow_one_add (s := 1/c n) (by linarith [hx n]) hp_lo
    have h2 := mul_le_mul_of_nonneg_left h1 (cpos n).le
    have e : c n * (1 + p*(1/c n)) = c n + p := by
      have hne := (cpos n).ne'
      field_simp
    rw [crec n]
    linarith
  have hup : ∀ n, c (n+1) - c n ≤ p + 1/c n := by
    intro n
    have h1 := bound (1/c n) (hx n).le
    have h4 := mul_le_mul_of_nonneg_left h1 (cpos n).le
    have e : c n * (1 + p*(1/c n) + (1/c n)^2) = c n + p + 1/c n := by
      have hne := (cpos n).ne'
      field_simp
    rw [e] at h4
    rw [crec n]
    linarith
  have hgrow : ∀ n : ℕ, c 0 + n*p ≤ c n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hlow n
      push_cast
      linarith
  have hcinf : Tendsto c atTop atTop := by
    apply tendsto_atTop_mono hgrow
    apply Filter.tendsto_atTop_add_const_left
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
  have hx_t : Tendsto (fun n => 1/c n) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hcinf
  have hd : Tendsto (fun n => c (n+1) - c n) atTop (𝓝 p) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlow hup
    have h := (tendsto_const_nhds (x := p)).add hx_t
    rw [add_zero] at h
    exact h
  have hces := hd.cesaro
  have h2 : (fun n : ℕ => (n:ℝ)⁻¹ * ∑ i ∈ Finset.range n, (c (i+1) - c i))
      = fun n : ℕ => (n:ℝ)⁻¹ * (c n - c 0) := by
    funext n
    rw [Finset.sum_range_sub]
  rw [h2] at hces
  have h3 : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * c 0) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (c 0)
    simpa using this
  have hcn : Tendsto (fun n : ℕ => c n / n) atTop (𝓝 p) := by
    have h4 := hces.add h3
    rw [add_zero] at h4
    have e : (fun n : ℕ => c n / n) = fun n : ℕ => (n:ℝ)⁻¹ * (c n - c 0) + (n:ℝ)⁻¹ * c 0 := by
      funext n; ring
    rw [e]; exact h4
  have hfun : ∀ n : ℕ, (a n)^(k+1)/((n:ℝ)^k) = (c n / n)^k := by
    intro n
    rw [div_pow, hc n]
    congr 1
    have : (a n ^ p)^k = a n ^ ((k:ℝ)+1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (apos n).le, hp]
      congr 1
      field_simp
    rw [this, show ((k:ℝ)+1) = ((k+1 : ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  have hsol : putnam_2006_b6_solution k = p^k := by
    simp [putnam_2006_b6_solution, hp]
  rw [hsol]
  have hT := hcn.pow k
  exact (tendsto_congr hfun).mpr hT
