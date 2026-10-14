import Mathlib

open Set Function Filter Topology

lemma cdiv (B : ℕ) (hB : 0 < B) : B.divisors.card ≤ 2 * Nat.sqrt B := by
  set s := Nat.sqrt B
  have h1 : (B.divisors.filter (· ≤ s)).card ≤ s := by
    calc _ ≤ (Finset.Icc 1 s).card := by
          apply Finset.card_le_card
          intro d hd
          simp only [Finset.mem_filter, Nat.mem_divisors] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 hB, hd.2⟩
      _ = s := by simp
  have h2 : (B.divisors.filter (fun d => ¬ d ≤ s)).card ≤ s := by
    calc _ ≤ (Finset.Icc 1 s).card := by
          apply Finset.card_le_card_of_injOn (fun d => B / d)
          · intro d hd
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd
            obtain ⟨⟨hd1, _⟩, hd2⟩ := hd
            simp only [Finset.coe_Icc, Set.mem_Icc]
            have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd1 hB
            obtain ⟨k, hk⟩ := hd1
            have : B / d = k := by rw [hk]; exact Nat.mul_div_cancel_left _ hdp
            rw [this]
            have kp : 0 < k := by
              rcases Nat.eq_zero_or_pos k with h | h
              · subst h; omega
              · exact h
            refine ⟨kp, ?_⟩
            by_contra hc
            have h3 : s + 1 ≤ k := by omega
            have h4 : s + 1 ≤ d := by omega
            have : B < (s+1)*(s+1) := Nat.lt_succ_sqrt B
            have : (s+1)*(s+1) ≤ d * k := Nat.mul_le_mul h4 h3
            omega
          · intro d hd e he hde
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd he
            simp only at hde
            have h3 := Nat.div_mul_cancel hd.1.1
            have h4 := Nat.div_mul_cancel he.1.1
            have hp : 0 < B / d := Nat.div_pos (Nat.le_of_dvd hB hd.1.1) (Nat.pos_of_dvd_of_pos hd.1.1 hB)
            rw [← hde] at h4
            exact Nat.eq_of_mul_eq_mul_left hp (h3.trans h4.symm)
      _ = s := by simp
  have := Finset.card_filter_add_card_filter_not (s := B.divisors) (fun d => d ≤ s)
  omega

theorem putnam_1964_b5
(a b : ℕ → ℕ)
(ha : StrictMono a ∧ ∀ n : ℕ, a n > 0)
(hb : b 0 = a 0 ∧ ∀ n : ℕ, b (n + 1) = lcm (b n) (a (n + 1)))
: (∃ L : ℝ, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) / b n) atTop (𝓝 L)) := by
  have hdvd : ∀ n i, i ≤ n → a i ∣ b n := by
    intro n
    induction n with
    | zero => intro i hi; obtain rfl : i = 0 := by omega
              rw [hb.1]
    | succ n ih =>
      intro i hi
      rw [hb.2]
      rcases Nat.lt_or_ge i (n+1) with h | h
      · exact (ih i (by omega)).trans (dvd_lcm_left _ _)
      · obtain rfl : i = n+1 := by omega
        exact dvd_lcm_right _ _
  have hpos : ∀ n, 0 < b n := by
    intro n
    induction n with
    | zero => rw [hb.1]; exact ha.2 0
    | succ n ih =>
      rw [hb.2]
      exact Nat.pos_of_ne_zero (fun h => by
        rcases Nat.lcm_eq_zero_iff.mp h with h | h
        · omega
        · exact (ha.2 _).ne' h)
  have hbd : ∀ n, (n+1)^2 ≤ 4 * b n := by
    intro n
    have hc : n + 1 ≤ (b n).divisors.card := by
      have : (Finset.image a (Finset.range (n+1))).card = n+1 := by
        rw [Finset.card_image_of_injective _ ha.1.injective]; simp
      rw [← this]
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact Nat.mem_divisors.mpr ⟨hdvd n i (by omega), (hpos n).ne'⟩
    have h1 := cdiv (b n) (hpos n)
    have h2 := Nat.sqrt_le' (b n)
    have : n + 1 ≤ 2 * Nat.sqrt (b n) := by omega
    calc (n+1)^2 ≤ (2 * Nat.sqrt (b n))^2 := Nat.pow_le_pow_left this 2
      _ = 4 * (Nat.sqrt (b n))^2 := by ring
      _ ≤ 4 * b n := by omega
  have hs : Summable (fun n : ℕ => (1:ℝ) / b n) := by
    have hs2 : Summable (fun n : ℕ => (4:ℝ) / ((n+1:ℕ):ℝ)^2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      simpa [div_eq_mul_inv] using this.mul_left 4
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs2
    have hp : (0:ℝ) < b n := by exact_mod_cast hpos n
    have h := hbd n
    have h' : (((n+1:ℕ):ℝ))^2 ≤ 4 * b n := by exact_mod_cast h
    rw [div_le_div_iff₀ hp (by positivity)]
    linarith
  exact ⟨_, hs.hasSum.tendsto_sum_nat⟩
