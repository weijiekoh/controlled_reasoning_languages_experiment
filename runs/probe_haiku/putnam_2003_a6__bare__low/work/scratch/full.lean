import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution := by
  classical
  -- r as a finite sum
  have hr' : ∀ S : Set ℕ, ∀ n : ℕ, r S n = ∑ a ∈ Finset.range (n+1), (if (a ≠ n - a ∧ a ∈ S ∧ n - a ∈ S) then 1 else 0 : ℕ) := by
    intro S n
    rw [hr]
    have h1 : ∀ x : S, ∑' s2 : S, (if (x ≠ s2 ∧ (x:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ)
        = ∑' s2 : ℕ, S.indicator (fun y => (if (x.1 ≠ y ∧ x.1 + y = n) then 1 else 0 : ℕ)) s2 := by
      intro x
      rw [← _root_.tsum_subtype S (fun y : ℕ => (if (x.1 ≠ y ∧ x.1 + y = n) then 1 else 0 : ℕ))]
      apply tsum_congr
      intro s2
      simp [Subtype.ext_iff]
    have h2 : ∀ x : ℕ, ∑' s2 : ℕ, S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2
        = ∑ s2 ∈ Finset.range (n+1), S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2 := by
      intro x
      apply tsum_eq_sum
      intro b hb
      simp only [Finset.mem_range, not_lt] at hb
      simp only [Set.indicator]
      split_ifs with h3 h4 <;> first | rfl | (exfalso; omega)
    simp only [h1]
    rw [_root_.tsum_subtype S (fun x : ℕ => ∑' s2 : ℕ, S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2)]
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    · apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_range] at ha
      simp only [h2]
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS]
        rw [Finset.sum_eq_single (n - a)]
        · by_cases hbS : n - a ∈ S
          · by_cases hne : a ≠ n - a
            · simp [Set.indicator, hne, haS, hbS]; omega
            · simp [Set.indicator, hne, haS, hbS]
          · simp [Set.indicator, hbS, haS]
        · intro b hb hbne
          simp only [Finset.mem_range] at hb
          simp only [Set.indicator]
          split_ifs with h3 h4 <;> first | rfl | (exfalso; omega)
        · intro h; exfalso; apply h; simp only [Finset.mem_range]; omega
      · simp [Set.indicator, haS]
    · intro b hb
      simp only [Finset.mem_range, not_lt] at hb
      have hz : ∀ s2 : ℕ, S.indicator (fun y => (if b ≠ y ∧ b + y = n then 1 else 0 : ℕ)) s2 = 0 := by
        intro s2
        simp only [Set.indicator]
        split_ifs with h3 h4 <;> first | rfl | (exfalso; omega)
      simp [hz]
  -- the Thue-Morse parity function
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, ∀ n, t n = (Nat.digits 2 n).sum % 2 := ⟨_, fun n => rfl⟩
  have ht_lt : ∀ n, t n < 2 := fun n => by rw [ht]; exact Nat.mod_lt _ (by norm_num)
  have ht0 : t 0 = 0 := by rw [ht]; simp
  have ht_even : ∀ m, t (2*m) = t m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [ht, ht, Nat.digits_def' (by norm_num) (by omega)]
      have h1 : 2*m % 2 = 0 := by omega
      have h2 : 2*m / 2 = m := by omega
      rw [h1, h2]; simp
  have ht_odd : ∀ m, t (2*m+1) = 1 - t m := by
    intro m
    have hm := ht_lt m
    rw [ht, ht, Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (2*m+1) % 2 = 1 := by omega
    have h2 : (2*m+1) / 2 = m := by omega
    rw [h1, h2]; simp
    omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℤ, ∀ n, ε n = if t n = 0 then 1 else -1 := ⟨_, fun n => rfl⟩
  have hε0 : ε 0 = 1 := by rw [hε, ht0]; simp
  have hεe : ∀ m, ε (2*m) = ε m := by intro m; rw [hε, hε, ht_even]
  have hεo : ∀ m, ε (2*m+1) = - ε m := by
    intro m
    rw [hε, hε, ht_odd]
    have := ht_lt m
    split_ifs <;> omega
  have hS : ∀ m, ∑ a ∈ Finset.range (2*m+1), ε a = ε m ∧ ∑ a ∈ Finset.range (2*m+2), ε a = 0 := by
    intro m
    induction m with
    | zero =>
      constructor
      · simp [hε0]
      · have h1 : ε 1 = -1 := by have := hεo 0; simp only [mul_zero, zero_add] at this; rw [this, hε0]
        show ∑ a ∈ Finset.range 2, ε a = 0
        simp [Finset.sum_range_succ, hε0, h1]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e1 : 2*(k+1)+1 = (2*k+2)+1 := by ring
      have e2 : 2*(k+1)+2 = (2*k+2)+1+1 := by ring
      have e3 : 2*k+2 = 2*(k+1) := by ring
      rw [e1, e2]
      constructor
      · have a1 : ε (2*k+2) = ε (k+1) := by rw [show 2*k+2 = 2*(k+1) by ring, hεe]
        rw [Finset.sum_range_succ, h2, a1]; simp
      · have a1 : ε (2*k+2) = ε (k+1) := by rw [show 2*k+2 = 2*(k+1) by ring, hεe]
        have a2 : ε (2*k+2+1) = -ε (k+1) := by rw [show 2*k+2+1 = 2*(k+1)+1 by ring, hεo]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, h2, a1, a2]; ring
  have hdiag : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hsplit : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then ε a else 0)
          = ε a - (if a = 2*m - a then ε a else 0) := by
        intro a _
        by_cases h : a = 2*m - a
        · rw [if_neg (not_not.mpr h), if_pos h, sub_self]
        · rw [if_pos (show a ≠ 2*m-a from h), if_neg h, sub_zero]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, (hS m).1]
      have hd : ∑ a ∈ Finset.range (2*m+1), (if a = 2*m - a then ε a else 0) = ε m := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
        · intro b hb hbm
          rw [if_neg]
          simp only [Finset.mem_range] at hb
          omega
        · intro h; exfalso; apply h; simp only [Finset.mem_range]; omega
      rw [hd, sub_self]
    · have hc : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then ε a else 0) = ε a := by
        intro a ha
        simp only [Finset.mem_range] at ha
        rw [if_pos (by omega)]
      rw [Finset.sum_congr rfl hc, show 2*m+1+1 = 2*m+2 by ring, (hS m).2]
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, A = {n | t n = 0} := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, B = {n | t n = 1} := ⟨_, rfl⟩
  have hAm : ∀ n, n ∈ A ↔ t n = 0 := fun n => by rw [hA]; exact Iff.rfl
  have hBm : ∀ n, n ∈ B ↔ t n = 1 := fun n => by rw [hB]; exact Iff.rfl
  refine ⟨A, B, ?_, ?_, ?_⟩
  · ext n
    simp only [Set.mem_union, Set.mem_univ, iff_true, hAm, hBm]
    have := ht_lt n
    omega
  · ext n
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, hAm, hBm]
    intro h1 h2
    omega
  · intro n
    rw [hr', hr']
    have term : ∀ a ∈ Finset.range (n+1),
        2 * ((if (a ≠ n - a ∧ a ∈ A ∧ n - a ∈ A) then 1 else 0 : ℕ) : ℤ)
        - 2 * ((if (a ≠ n - a ∧ a ∈ B ∧ n - a ∈ B) then 1 else 0 : ℕ) : ℤ)
        = (if a ≠ n - a then ε a else 0) + (if a ≠ n - a then ε (n - a) else 0) := by
      intro a _
      have hlt1 := ht_lt a
      have hlt2 := ht_lt (n - a)
      simp only [hAm, hBm, hε]
      by_cases hne : a ≠ n - a
      · by_cases h1 : t a = 0 <;> by_cases h2 : t (n - a) = 0 <;> simp [hne, h1, h2] <;> omega
      · simp [hne]
    have hsum' := Finset.sum_congr rfl term
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum'
    have hrefl : ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε (n - a) else 0)
        = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) := by
      have := Finset.sum_range_reflect (fun a => (if a ≠ n - a then ε a else 0)) (n+1)
      rw [← this]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_range] at ha
      rw [show n + 1 - 1 - a = n - a by omega, show n - (n - a) = a by omega]
      split_ifs with h1 h2 <;> first | rfl | omega
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sum, Nat.cast_sum]
    linarith [hsum', hrefl, hdiag n]
