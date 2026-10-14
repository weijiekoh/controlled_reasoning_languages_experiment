import Mathlib

open Set Function Filter Topology Polynomial Real

noncomputable abbrev putnam_1982_a2_solution : Prop := True
/--
Let $B_n(x) = 1^x + 2^x + \dots + n^x$ and let $f(n) = \frac{B_n(\log_n 2)}{(n \log_2 n)^2}$. Does $f(2) + f(3) + f(4) + \dots$ converge?
-/
theorem putnam_1982_a2
(B : ℕ → ℝ → ℝ)
(hB : B = fun (n : ℕ) (x : ℝ) ↦ ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ x)
(f : ℕ → ℝ)
(hf : f = fun n ↦ B n (logb n 2) / (n * logb 2 n) ^ 2)
: (∃ L : ℝ, Tendsto (fun N ↦ ∑ j ∈ Finset.Icc 2 N, f j) atTop (𝓝 L)) ↔ putnam_1982_a2_solution :=
  by
  simp only [iff_true]
  set g : ℕ → ℝ := fun n => 1 / ((max n 2 : ℕ) * (Real.log (max n 2 : ℕ))^2) with hg
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have gnn : ∀ n, 0 ≤ g n := fun n => by positivity
  have ganti : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → g n ≤ g m := by
    intro m n _ hmn
    simp only [hg]
    have h2 : (2:ℝ) ≤ ((max m 2 : ℕ):ℝ) := by exact_mod_cast le_max_right _ _
    have hle : ((max m 2 : ℕ):ℝ) ≤ ((max n 2 : ℕ):ℝ) := by exact_mod_cast max_le_max hmn le_rfl
    have lm : 0 < Real.log ((max m 2 : ℕ):ℝ) := Real.log_pos (by linarith)
    have lle := Real.log_le_log (by linarith) hle
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul hle (by gcongr) (by positivity) (by linarith)
  have hs : Summable g := by
    rw [← summable_condensed_iff_of_nonneg gnn ganti]
    rw [← summable_nat_add_iff 1]
    have : Summable (fun k : ℕ => (1 / Real.log 2 ^ 2) * (1 / ((k:ℝ)+1) ^ 2)) := by
      apply Summable.mul_left
      have := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      rw [← summable_nat_add_iff 1] at this
      simpa using this
    refine this.congr (fun k => ?_)
    simp only [hg]
    have : max (2^(k+1)) 2 = 2^(k+1) := max_eq_left (by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]
    push_cast
    rw [Real.log_pow]
    push_cast
    have : (0:ℝ) < 2^(k+1) := by positivity
    field_simp
  have hs2 : Summable (fun k : ℕ => f (k+2)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((summable_nat_add_iff 2).2 hs |>.mul_left (2 * Real.log 2 ^ 2))
    · subst hf hB
      have : (0:ℝ) < Real.log ((k+2:ℕ):ℝ) := Real.log_pos (by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      simp only
      apply div_nonneg
      · apply Finset.sum_nonneg; intro i _; positivity
      · positivity
    · subst hf hB
      simp only [hg]
      have hm : max (k+2) 2 = k+2 := max_eq_left (by omega)
      rw [hm]
      set n : ℕ := k+2 with hn
      have hn2 : (2:ℝ) ≤ n := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have ln : 0 < Real.log n := Real.log_pos (by linarith)
      have hB : (∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ (logb n 2)) ≤ 2 * n := by
        calc _ ≤ ∑ i ∈ Finset.Icc 1 n, (n:ℝ) ^ (logb n 2) := by
              apply Finset.sum_le_sum; intro i hi
              have := Finset.mem_Icc.1 hi
              apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast this.2)
              unfold logb; exact div_nonneg l2.le ln.le
          _ = 2 * n := by
              rw [Real.rpow_logb (by linarith) (by linarith) (by norm_num)]
              simp; ring
      have hd : (n * logb 2 n) ^ 2 = n^2 * Real.log n ^ 2 / Real.log 2 ^ 2 := by
        unfold logb; field_simp
      rw [hd]
      have npos : (0:ℝ) < n := by linarith
      calc _ ≤ 2 * n / (n^2 * Real.log n ^ 2 / Real.log 2 ^ 2) := by
            gcongr
        _ = _ := by field_simp
  have hs3 : Summable f := (summable_nat_add_iff 2).1 hs2
  refine ⟨∑' k, f (k+2), ?_⟩
  have h1 := hs2.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => N+1-2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b+2, fun a ha => by omega⟩
  refine (h1.comp h2).congr (fun N => ?_)
  simp only [Function.comp]
  have e : Finset.Icc 2 N = Finset.Ico 2 (N+1) := by ext; simp
  rw [e, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]
