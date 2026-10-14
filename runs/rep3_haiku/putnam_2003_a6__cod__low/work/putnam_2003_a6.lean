import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution :=by
  classical
  have hs : ∀ n : ℕ, (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n/2)).sum := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by norm_num) hn]; simp
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℤ, ∀ n, x n = if (Nat.digits 2 n).sum % 2 = 0 then 1 else 0 :=
    ⟨_, fun n => rfl⟩
  have hx0 : ∀ m, x (2*m) = x m := by
    intro m
    rw [hx, hx, hs (2*m), show 2*m % 2 = 0 by omega, show 2*m/2 = m by omega]
    simp
  have hx1 : ∀ m, x (2*m+1) = 1 - x m := by
    intro m
    rw [hx, hx, hs (2*m+1), show (2*m+1) % 2 = 1 by omega, show (2*m+1)/2 = m by omega]
    split_ifs <;> omega
  have hS : ∀ m : ℕ, ∑ a ∈ Finset.range (2*m), x a = (m:ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = 2*k+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, hx0, hx1]
      push_cast; ring
  have hS' : ∀ m : ℕ, ∑ a ∈ Finset.range (2*m+1), x a = (m:ℤ) + x m := by
    intro m; rw [Finset.sum_range_succ, hS, hx0]
  have hkey : ∀ n : ℕ, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then x a + x (n-a) - 1 else 0) = 0 := by
    intro n
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h1 : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then x a + x (2*m-a) - 1 else 0)
          = (x a + x (2*m-a) - 1) - (if a = m then (x a + x (2*m-a) - 1) else 0) := by
        intro a ha
        have ha' := Finset.mem_range.mp ha
        by_cases h : a = m
        · subst h
          have hn : ¬ (a ≠ 2*a - a) := by omega
          rw [if_neg hn, if_pos rfl]; ring
        · rw [if_pos (show a ≠ 2*m - a by omega), if_neg h]; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      rw [if_pos (show m < 2*m+1 by omega)]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hr2 : ∑ a ∈ Finset.range (2*m+1), x (2*m-a) = ∑ a ∈ Finset.range (2*m+1), x a := by
        have := Finset.sum_range_reflect x (2*m+1)
        rw [← this]; apply Finset.sum_congr rfl; intro a _; congr 1 <;> omega
      rw [hr2, hS', show 2*m - m = m by omega]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; ring
    · have h1 : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then x a + x (2*m+1-a) - 1 else 0)
          = x a + x (2*m+1-a) - 1 := by
        intro a ha
        have ha' := Finset.mem_range.mp ha
        rw [if_pos (show a ≠ 2*m+1-a by omega)]
      rw [Finset.sum_congr rfl h1]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hr2 : ∑ a ∈ Finset.range (2*m+1+1), x (2*m+1-a) = ∑ a ∈ Finset.range (2*m+1+1), x a := by
        have := Finset.sum_range_reflect x (2*m+1+1)
        rw [← this]; apply Finset.sum_congr rfl; intro a _; congr 1 <;> omega
      have hS2 : ∑ a ∈ Finset.range (2*m+1+1), x a = (m:ℤ) + 1 := by
        rw [show 2*m+1+1 = 2*(m+1) by omega, hS]; push_cast; ring
      rw [hr2, hS2]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; ring
  have hcol : ∀ n a : ℕ, a ∈ Finset.range (n+1) →
      ∑ b ∈ Finset.range (n+1), (if a ≠ b ∧ a + b = n then x a + x b - 1 else 0)
        = (if a ≠ n - a then x a + x (n-a) - 1 else 0) := by
    intro n a ha
    have ha' := Finset.mem_range.mp ha
    rw [Finset.sum_eq_single (n-a)]
    · by_cases h : a ≠ n - a
      · have hc : a ≠ n - a ∧ a + (n - a) = n := ⟨h, by omega⟩
        rw [if_pos hc, if_pos h]
      · rw [if_neg (fun h' : a ≠ n - a ∧ a + (n - a) = n => h h'.1), if_neg h]
    · intro b _ hne
      rw [if_neg (fun h' : a ≠ b ∧ a + b = n => hne (by have := h'.2; omega))]
    · intro h
      exact absurd (Finset.mem_range.mpr (show n - a < n+1 by omega)) h
  have hmain : ∀ n : ℕ, ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a ≠ b ∧ a + b = n then x a + x b - 1 else 0) = 0 := by
    intro n
    have e : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if a ≠ b ∧ a + b = n then x a + x b - 1 else 0)
        = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then x a + x (n-a) - 1 else 0) :=
      Finset.sum_congr rfl (fun a ha => hcol n a ha)
    rw [e]; exact hkey n
  have hconv : ∀ S : Set ℕ, ∀ n, r S n = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n then 1 else 0) := by
    intro S n
    rw [hr]
    have key : ∀ (f : ℕ → ℕ) (N : ℕ), (∀ y, N ≤ y → f y = 0) → ∑' y, f y = ∑ y ∈ Finset.range N, f y := by
      intro f N hf
      apply tsum_eq_sum
      intro y hy
      exact hf y (by simpa using hy)
    have h0 : ∀ a s2 : ℕ, (n < a ∨ n < s2) →
        S.indicator (fun s2 => if ¬ a = s2 ∧ a + s2 = n then (1:ℕ) else 0) s2 = 0 := by
      intro a s2 h
      by_cases hS2 : s2 ∈ S
      · rw [Set.indicator_of_mem hS2, if_neg (show ¬ (¬ a = s2 ∧ a + s2 = n) from fun h' => by omega)]
      · simp [Set.indicator_apply, hS2]
    have hinner : ∀ n1 : ℕ, (∑' s2 : S, if (¬ n1 = (s2:ℕ) ∧ n1 + (s2:ℕ) = n) then 1 else 0)
        = ∑' s2 : ℕ, S.indicator (fun s2 => if ¬ n1 = s2 ∧ n1 + s2 = n then 1 else 0) s2 :=
      fun n1 => tsum_subtype S (fun n2 : ℕ => if ¬ n1 = n2 ∧ n1 + n2 = n then 1 else 0)
    simp only [ne_eq, Subtype.ext_iff, hinner]
    rw [tsum_subtype S (fun n1 : ℕ => ∑' s2 : ℕ, S.indicator (fun s2 => if ¬ n1 = s2 ∧ n1 + s2 = n then 1 else 0) s2)]
    rw [key _ (n+1)]
    · apply Finset.sum_congr rfl
      intro a _
      by_cases hA : a ∈ S
      · rw [Set.indicator_of_mem hA, key _ (n+1)]
        · apply Finset.sum_congr rfl
          intro b _
          by_cases hB : b ∈ S <;> simp [Set.indicator_apply, hA, hB]
        · intro y hy
          exact h0 a y (Or.inr (by omega))
      · simp [hA]
    · intro y hy
      rw [Set.indicator_apply]
      split_ifs
      · have : ∀ s2 : ℕ, S.indicator (fun s2 => if ¬ y = s2 ∧ y + s2 = n then (1:ℕ) else 0) s2 = 0 :=
          fun s2 => h0 y s2 (Or.inl (by omega))
        simp [this]
      · rfl
  have main : ∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n) := by
    refine ⟨{n | (Nat.digits 2 n).sum % 2 = 0}, {n | ¬ ((Nat.digits 2 n).sum % 2 = 0)}, ?_, ?_, ?_⟩
    · exact Set.eq_univ_of_forall (fun n => by by_cases h : (Nat.digits 2 n).sum % 2 = 0 <;> [exact Or.inl h; exact Or.inr h])
    · ext n; simp
    · intro n
      rw [hconv, hconv]
      apply @Nat.cast_injective ℤ
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have hdiff : (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if a ∈ {n | (Nat.digits 2 n).sum % 2 = 0} ∧ b ∈ {n | (Nat.digits 2 n).sum % 2 = 0} ∧ a ≠ b ∧ a + b = n then (1:ℤ) else 0))
          - (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if a ∈ {n | ¬ ((Nat.digits 2 n).sum % 2 = 0)} ∧ b ∈ {n | ¬ ((Nat.digits 2 n).sum % 2 = 0)} ∧ a ≠ b ∧ a + b = n then (1:ℤ) else 0))
          = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if a ≠ b ∧ a + b = n then x a + x b - 1 else 0) := by
        simp only [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        rw [hx a, hx b]
        simp only [Set.mem_setOf_eq]
        split_ifs <;> omega
      have := hmain n
      linarith
  exact iff_of_true main trivial
