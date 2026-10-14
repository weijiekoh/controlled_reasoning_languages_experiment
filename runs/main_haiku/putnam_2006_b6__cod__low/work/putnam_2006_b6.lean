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
  classical
  set p : ℝ := ((k:ℝ)+1)/k with hp_def
  have hkgt : (1:ℝ) < k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hp : 0 < p := by rw [hp_def]; positivity
  have hpk : p * k = k + 1 := by rw [hp_def]; field_simp
  have h1p : 1 - p = -((1:ℝ)/k) := by rw [hp_def]; field_simp; ring
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha n]
      have : 0 < 1/((a n)^((1:ℝ)/k)) := by
        apply one_div_pos.mpr; exact Real.rpow_pos_of_pos ih _
      linarith
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro n
    rw [ha n]
    have : 0 < 1/((a n)^((1:ℝ)/k)) := by
      apply one_div_pos.mpr; exact Real.rpow_pos_of_pos (hpos n) _
    linarith
  have hunb : Tendsto a atTop atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone hmono
    intro B
    by_contra h
    push Not at h
    set M : ℝ := max B 1 with hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    set δ : ℝ := 1 / M^((1:ℝ)/k) with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact one_div_pos.mpr (Real.rpow_pos_of_pos hMpos _)
    have key : ∀ n : ℕ, a 0 + n * δ ≤ a n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ha n]
        have hlt : a n < M := lt_of_lt_of_le (h n) (le_max_left _ _)
        have hle : (a n)^((1:ℝ)/k) ≤ M^((1:ℝ)/k) :=
          Real.rpow_le_rpow (hpos n).le hlt.le (by positivity)
        have : δ ≤ 1/((a n)^((1:ℝ)/k)) := by
          apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hpos n) _) hle
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (B / δ)
    have h2 : B < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
    have := key n
    have := hpos 0
    linarith [h n]
  set b : ℕ → ℝ := fun n => (a n)^p with hb_def
  have hbtop : Tendsto b atTop atTop := by
    exact (tendsto_rpow_atTop hp).comp hunb
  have hderiv : HasDerivAt (fun x : ℝ => (1+x)^p) p 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).const_add 1).rpow_const (p := p) (Or.inl (by norm_num))
    convert h using 1
    simp
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hF0 : (fun x : ℝ => (1+x)^p) 0 = 1 := by simp
  have hx : Tendsto (fun n => (b n)⁻¹) atTop (𝓝 0) := hbtop.inv_tendsto_atTop
  have hxne : Tendsto (fun n => (b n)⁻¹) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx, ?_⟩
    apply Eventually.of_forall
    intro n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
    exact (Real.rpow_pos_of_pos (hpos n) _).ne'
  have hdiff : Tendsto (fun n => b (n+1) - b n) atTop (𝓝 p) := by
    have hcomp := hslope.comp hxne
    apply hcomp.congr
    intro n
    simp only [Function.comp, slope_def_field, hF0]
    have hA : a (n+1) = a n * (1 + (b n)⁻¹) := by
      rw [ha n]
      have hinv : (b n)⁻¹ = (a n)^(-p) := by
        rw [hb_def]; exact (Real.rpow_neg (hpos n).le p).symm
      rw [hinv]
      have e1 : (a n)^(1:ℝ) * (a n)^(-p) = (a n)^(1 + -p) := (Real.rpow_add (hpos n) _ _).symm
      rw [Real.rpow_one, show 1 + -p = -((1:ℝ)/k) by linarith [h1p],
        Real.rpow_neg (hpos n).le ((1:ℝ)/k)] at e1
      rw [mul_add, mul_one, e1, one_div]
    have hsucc : b (n+1) = b n * (1 + (b n)⁻¹ ) ^ p := by
      rw [hb_def]
      simp only
      rw [hA, Real.mul_rpow (hpos n).le (add_pos one_pos (inv_pos.mpr (Real.rpow_pos_of_pos (hpos n) p))).le]
    rw [sub_zero, hsucc]
    field_simp
  have hces := hdiff.cesaro
  simp_rw [Finset.sum_range_sub] at hces
  have hr := hces.add ((tendsto_one_div_atTop_nhds_zero_nat).const_mul (b 0))
  rw [mul_zero, add_zero] at hr
  have hratio : Tendsto (fun n:ℕ => b n / n) atTop (𝓝 p) :=
    hr.congr (fun n => by ring)
  have hfin := hratio.pow k
  have heq : (fun n:ℕ => (a n)^(k+1)/((n:ℝ)^k)) = fun n => (b n / n)^k := by
    funext n
    rw [div_pow]
    congr 1
    rw [hb_def]
    simp only
    rw [← Real.rpow_natCast (a n ^ p) k, ← Real.rpow_mul (hpos n).le, hpk]
    rw [show ((k:ℝ)+1) = ((k+1 : ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  simp only [putnam_2006_b6_solution]
  rw [heq]
  exact hfin
