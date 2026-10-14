import Mathlib

open Matrix Function Real Topology Filter

noncomputable abbrev putnam_2012_b4_solution : Prop := True
/--
Suppose that $a_0 = 1$ and that $a_{n+1} = a_n + e^{-a_n}$ for $n=0,1,2,\dots$. Does $a_n - \log n$
have a finite limit as $n \to \infty$? (Here $\log n = \log_e n = \ln n$.)
-/
theorem putnam_2012_b4
(a : ℕ → ℝ)
(ha0 : a 0 = 1)
(han : ∀ n : ℕ, a (n + 1) = a n + exp (-a n))
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) :=
by
  have hge : ∀ n : ℕ, 1 ≤ a n := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih => rw [han n]; have := exp_pos (-a n); linarith
  have hcu : ∀ n : ℕ, exp (a n) * exp (-a n) = 1 := by
    intro n; rw [← exp_add]; simp
  have hstep : ∀ n : ℕ, exp (a (n+1)) = exp (a n) * exp (exp (-a n)) := by
    intro n; rw [han n, exp_add]
  have hlow : ∀ n : ℕ, (n:ℝ) + exp 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      have h1 := add_one_le_exp (exp (-a n))
      have h2 := hcu n
      have h4 : exp (a n) * (exp (-a n) + 1) ≤ exp (a n) * exp (exp (-a n)) :=
        mul_le_mul_of_nonneg_left h1 (exp_pos _).le
      rw [hstep n]; push_cast; nlinarith
  have hup : ∀ n : ℕ, exp (a (n+1)) ≤ exp (a n) + 1 + exp (-a n) := by
    intro n
    have hy1 : exp (-a n) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hge n])
    have hy0 : 0 ≤ exp (-a n) := (exp_pos _).le
    have hb := abs_le.mp (abs_exp_sub_one_sub_id_le (x := exp (-a n))
      (by rw [abs_of_nonneg hy0]; exact hy1))
    have h2 := hcu n
    have h5 : exp (a n) * exp (-a n)^2 = exp (-a n) := by linear_combination (exp (-a n)) * h2
    have h6 : exp (a n) * (1 + exp (-a n) + exp (-a n)^2) = exp (a n) + 1 + exp (-a n) := by
      linear_combination h2 + h5
    have h4 : exp (a n) * exp (exp (-a n)) ≤ exp (a n) * (1 + exp (-a n) + exp (-a n)^2) :=
      mul_le_mul_of_nonneg_left (by linarith [hb.2]) (exp_pos _).le
    rw [hstep n]; linarith
  have hlogstep : ∀ y : ℝ, 0 < y → 1/(y+1) ≤ Real.log (y+1) - Real.log y := by
    intro y hy
    have h := log_le_sub_one_of_pos (show 0 < y/(y+1) by positivity)
    rw [log_div (ne_of_gt hy) (by positivity)] at h
    have h2 : y/(y+1) - 1 = -(1/(y+1)) := by rw [div_sub_one (by positivity)]; ring
    linarith
  have he2 : (2:ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1:ℝ)]
  have hD : ∀ n : ℕ, exp (a n) - n ≤ exp 1 + 2 * Real.log ((n:ℝ) + exp 1) - 2 := by
    intro n
    induction n with
    | zero => norm_num [ha0, log_exp]
    | succ n ih =>
      have hx := hcu n
      have hlo := hlow n
      have hxpos := exp_pos (-a n)
      have hy0 : (0:ℝ) < (n:ℝ) + exp 1 := by positivity
      have hn0' : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hy1 : (1:ℝ) ≤ (n:ℝ) + exp 1 := by linarith
      have hxy : exp (-a n) * ((n:ℝ) + exp 1) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hlo hxpos.le
        nlinarith
      have h1 : exp (-a n) ≤ 1 / ((n:ℝ) + exp 1) := by
        rw [le_div_iff₀ hy0]; linarith
      have h2 : 1 / ((n:ℝ) + exp 1) ≤ 2 * (1 / ((n:ℝ) + exp 1 + 1)) := by
        rw [show 2 * (1 / ((n:ℝ) + exp 1 + 1)) = 1 / (((n:ℝ) + exp 1 + 1)/2) by
          field_simp]
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      have h3 := hlogstep ((n:ℝ) + exp 1) hy0
      have e' : (n:ℝ) + exp 1 + 1 = (n:ℝ) + 1 + exp 1 := by ring
      rw [e'] at h3 h2
      have hup' := hup n
      push_cast
      linarith
  have hlogbd : ∀ n : ℕ, 1 ≤ n →
      Real.log ((n:ℝ) + exp 1) ≤ 2 * (1 + exp 1)^((1:ℝ)/2) * (n:ℝ)^((1:ℝ)/2) := by
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    have h := log_le_rpow_div (x := (n:ℝ) + exp 1) (ε := (1:ℝ)/2) (by positivity) (by norm_num)
    have h2 : ((n:ℝ) + exp 1)^((1:ℝ)/2) ≤ ((1 + exp 1) * n)^((1:ℝ)/2) :=
      rpow_le_rpow (by positivity) (by nlinarith [exp_pos 1]) (by norm_num)
    rw [mul_rpow (by positivity) hn0.le] at h2
    have h3 : ((n:ℝ) + exp 1)^((1:ℝ)/2) / ((1:ℝ)/2) = 2 * ((n:ℝ) + exp 1)^((1:ℝ)/2) := by ring
    rw [h3] at h
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = exp 1 + 4 * (1 + exp 1)^((1:ℝ)/2) := ⟨_, rfl⟩
  have hDbd : ∀ n : ℕ, 1 ≤ n → exp (a n) - n + 1 ≤ K * (n:ℝ)^((1:ℝ)/2) := by
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have h1 := hD n
    have h2 := hlogbd n hn
    have hr1 : (1:ℝ) ≤ (n:ℝ)^((1:ℝ)/2) := one_le_rpow hn1 (by norm_num)
    have he1 : exp 1 ≤ exp 1 * (n:ℝ)^((1:ℝ)/2) := by nlinarith [exp_pos 1]
    rw [hKdef]
    nlinarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ → ℝ, ∀ n, x n = a n - Real.log n := ⟨fun n => a n - Real.log n, fun n => rfl⟩
  have hT : ∀ n : ℕ, 1 ≤ n → |x (n+1) - x n| ≤ K * (1 / (n:ℝ)^((3:ℝ)/2)) := by
    intro n hn
    rw [hxdef, hxdef]
    push_cast
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    have hA : a (n+1) = a n + exp (-a n) := han n
    have hc := hlow n
    have hcu' := hcu n
    have hDr := hDbd n hn
    rw [hA]
    have hr2 : ((n:ℝ)^((1:ℝ)/2))^2 = n := by
      rw [← rpow_natCast, ← rpow_mul hn0.le]; norm_num
    have hn32 : (n:ℝ)^((3:ℝ)/2) = n * (n:ℝ)^((1:ℝ)/2) := by
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, rpow_add hn0, rpow_one]
    set c := exp (a n) with hcdef
    set u := exp (-a n) with hudef
    set r := (n:ℝ)^((1:ℝ)/2) with hrdef
    have hu0 : 0 < u := exp_pos _
    have hD0 : (0:ℝ) ≤ c - n := by linarith [exp_pos 1]
    have hu_n : u * n ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (show (n:ℝ) ≤ c by linarith [exp_pos 1]) hu0.le
      nlinarith
    have hw : (1/(n:ℝ)) * n = 1 := by field_simp
    have key1 : (1/(n:ℝ) - u) * (n:ℝ)^2 = u * n * (c - n) := by
      linear_combination (n:ℝ) * hw - (n:ℝ) * hcu'
    have hlow1 : 0 ≤ 1/(n:ℝ) - u := by
      have h0 : 0 ≤ (1/(n:ℝ) - u) * (n:ℝ)^2 := by
        rw [key1]; exact mul_nonneg (mul_nonneg hu0.le hn0.le) hD0
      exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h0
    have hup1 : 1/(n:ℝ) - u ≤ (c - n) / (n:ℝ)^2 := by
      have h0 : (1/(n:ℝ) - u) * (n:ℝ)^2 ≤ ((c - n) / (n:ℝ)^2) * (n:ℝ)^2 := by
        rw [key1, div_mul_cancel₀ _ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hu_n) hD0]
      exact le_of_mul_le_mul_right h0 (by positivity)
    have hL1 := hlogstep (n:ℝ) hn0
    have hL2 : Real.log ((n:ℝ)+1) - Real.log n ≤ 1/(n:ℝ) := by
      have h := log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/n by positivity)
      rw [log_div (by positivity) (ne_of_gt hn0)] at h
      have h2 : ((n:ℝ)+1)/n - 1 = 1/n := by rw [div_sub_one (ne_of_gt hn0)]; ring
      linarith
    have hL3 : 1/(n:ℝ) - 1/((n:ℝ)+1) ≤ 1/(n:ℝ)^2 := by
      rw [div_sub_div _ _ (ne_of_gt hn0) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hpos2 : 0 ≤ 1/(n:ℝ)^2 := by positivity
    have hDn : 0 ≤ (c - n)/(n:ℝ)^2 := div_nonneg hD0 (by positivity)
    have hsplit : (c - n + 1)/(n:ℝ)^2 = (c - n)/(n:ℝ)^2 + 1/(n:ℝ)^2 := by ring
    have hbound : |u - (Real.log ((n:ℝ)+1) - Real.log n)| ≤ (c - n + 1)/(n:ℝ)^2 := by
      rw [abs_le]; constructor <;> linarith
    have hr : c - n + 1 ≤ K * r := hDr
    have hfin : (c - n + 1)/(n:ℝ)^2 ≤ K * r / (n:ℝ)^2 :=
      div_le_div_of_nonneg_right hr (by positivity)
    have hkey : K * r / (n:ℝ)^2 = K * (1 / (n * r)) := by
      rw [show (n:ℝ)^2 = (n * r) * r by linear_combination (-(n:ℝ)) * hr2]
      field_simp
    rw [hn32]
    calc _ = |u - (Real.log ((n:ℝ)+1) - Real.log n)| := by congr 1; ring
      _ ≤ (c - n + 1)/(n:ℝ)^2 := hbound
      _ ≤ K * r / (n:ℝ)^2 := hfin
      _ = K * (1 / (n * r)) := hkey
  have hsumm : Summable (fun k : ℕ => K * (1 / ((k+1 : ℕ):ℝ)^((3:ℝ)/2))) := by
    apply Summable.mul_left
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr (by norm_num))
  have hS : Summable (fun k : ℕ => x (k+1+1) - x (k+1)) :=
    Summable.of_norm_bounded hsumm (fun k => by
      rw [Real.norm_eq_abs]; exact hT (k+1) (by omega))
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, (x (k+1+1) - x (k+1)) = x (N+1) - x 1 := by
    intro N
    have := Finset.sum_range_sub (fun k => x (k+1)) N
    simp only [zero_add] at this
    exact this
  have hlim : Filter.Tendsto (fun N : ℕ => x (N+1)) Filter.atTop
      (nhds (x 1 + ∑' k, (x (k+1+1) - x (k+1)))) := by
    have h2 := (hS.hasSum.tendsto_sum_nat).const_add (x 1)
    exact Filter.Tendsto.congr (fun N => by rw [hpart N]; ring) h2
  have hfin : Filter.Tendsto x Filter.atTop (nhds (x 1 + ∑' k, (x (k+1+1) - x (k+1)))) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
  have hfun : (fun n : ℕ => a n - Real.log n) = x := funext fun n => (hxdef n).symm
  simp only [putnam_2012_b4_solution]
  exact iff_true_intro ⟨_, by rw [hfun]; exact hfin⟩
