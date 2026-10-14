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
  have hkR : (1:ℝ) < k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((k:ℝ)+1)/k := ⟨_, rfl⟩
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hkpos]; linarith
  have hp0 : 0 < p := by linarith
  have hpk : p * (k:ℝ) = (k:ℝ) + 1 := by rw [hp]; field_simp
  have hapos : ∀ n, a n > 0 := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha n]
      have : 0 < 1/((a n)^((1:ℝ)/k)) := div_pos one_pos (Real.rpow_pos_of_pos ih _)
      linarith
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun n => (a n)^p := ⟨_, rfl⟩
  have hupos : ∀ n, u n > 0 := by
    intro n; rw [hu]; exact Real.rpow_pos_of_pos (hapos n) _
  have h1 : ∀ n, (a n)^p = a n * (a n)^((1:ℝ)/k) := by
    intro n
    rw [hp, show ((k:ℝ)+1)/k = 1 + 1/k by field_simp, Real.rpow_add (hapos n), Real.rpow_one]
  have hu_rec : ∀ n, u (n+1) = u n * (1 + 1/u n)^p := by
    intro n
    have hA : u (n+1) = (a (n+1))^p := by rw [hu]
    have hB : u n = (a n)^p := by rw [hu]
    have hq : 0 ≤ 1 + 1/u n := by
      have := one_div_pos.mpr (hupos n); linarith
    have h2 : a (n+1) = a n * (1 + 1/u n) := by
      rw [ha n, hB, h1 n]
      have hx : 0 < (a n)^((1:ℝ)/k) := Real.rpow_pos_of_pos (hapos n) _
      have hx1 := hx.ne'
      have hx2 := (hapos n).ne'
      field_simp
    rw [hA, h2, Real.mul_rpow (hapos n).le hq, ← hB]
  have hbern : ∀ n, u n + p ≤ u (n+1) := by
    intro n
    have ht : -1 ≤ 1/u n := by
      have := one_div_pos.mpr (hupos n); linarith
    have hB := one_add_mul_self_le_rpow_one_add ht hp1.le
    have hpos := hupos n
    have e : u n + p = u n * (1 + p * (1/u n)) := by
      field_simp
    rw [hu_rec n, e]
    exact mul_le_mul_of_nonneg_left hB hpos.le
  have hlb : ∀ n : ℕ, u 0 + p * n ≤ u n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      linarith [hbern n]
  have hut : Tendsto u atTop atTop :=
    tendsto_atTop_mono hlb (tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop hp0))
  have hinv : Tendsto (fun n => (u n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hut
  have hd : HasDerivAt (fun t:ℝ => (1+t)^p) p 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const (p := p) (Or.inr hp1.le)
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd
  have hslope' : Tendsto (fun t:ℝ => ((1+t)^p - 1)/t) (𝓝[≠] 0) (𝓝 p) := by
    refine hslope.congr (fun t => ?_)
    simp only [zero_add, add_zero, Real.one_rpow, smul_eq_mul]
    rw [div_eq_inv_mul]
  have ht : Tendsto (fun n => (u n)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hinv, Eventually.of_forall (fun n => inv_ne_zero (hupos n).ne')⟩
  have hratio := hslope'.comp ht
  have hdiff : Tendsto (fun n => u (n+1) - u n) atTop (𝓝 p) := by
    refine hratio.congr (fun n => ?_)
    show ((1 + (u n)⁻¹)^p - 1)/(u n)⁻¹ = u (n+1) - u n
    rw [div_inv_eq_mul, hu_rec n, one_div]; ring
  have hcs := hdiff.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (u (i+1) - u i) = u n - u 0 :=
    fun n => Finset.sum_range_sub u n
  have hc2 : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * (u n - u 0)) atTop (𝓝 p) :=
    hcs.congr (fun n => by rw [hsum n])
  have h4 := hc2.add (tendsto_const_div_atTop_nhds_zero_nat (u 0))
  rw [add_zero] at h4
  have hdiv : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 p) :=
    h4.congr (fun n => by ring)
  have hfin := hdiv.pow k
  have hsol : p^k = putnam_2006_b6_solution k := by
    rw [hp]
  rw [← hsol]
  refine hfin.congr (fun n => ?_)
  have hpow : (u n)^k = (a n)^(k+1) := by
    rw [hu]
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hapos n).le, hpk]
    norm_cast
  rw [div_pow, hpow]
