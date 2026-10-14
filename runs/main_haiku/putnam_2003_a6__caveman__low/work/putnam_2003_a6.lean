import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution :=
by
  classical
  obtain ⟨s, hsev, hsodd, hspm⟩ : ∃ s : ℕ → ℤ, (∀ m, s (2*m) = s m) ∧ (∀ m, s (2*m+1) = - s m) ∧ (∀ n, s n = 1 ∨ s n = -1) := by
    refine ⟨fun n => (-1:ℤ)^((Nat.digits 2 n).count 1), ?_, ?_, ?_⟩
    · intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · simp only
        rw [Nat.digits_def' (by norm_num) (by omega), show 2*m % 2 = 0 by omega, show 2*m/2 = m by omega]
        simp
    · intro m
      simp only
      rw [Nat.digits_def' (by norm_num) (by omega), show (2*m+1) % 2 = 1 by omega, show (2*m+1)/2 = m by omega]
      simp [List.count_cons, pow_succ]
    · intro n
      exact neg_one_pow_eq_or ℤ _
  have L1 : ∀ m, ∑ i ∈ Finset.range (2*m), s i = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = 2*k+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, hsev, hsodd]
      ring
  have L2 : ∀ m, ∑ i ∈ Finset.range (2*m+1), s i = s m := by
    intro m
    rw [Finset.sum_range_succ, L1, hsev, zero_add]
  have refl : ∀ n, ∑ a ∈ Finset.range (n+1), s (n-a) = ∑ a ∈ Finset.range (n+1), s a := by
    intro n
    simpa using Finset.sum_range_reflect s (n+1)
  have Z : ∀ n, ∑ a ∈ Finset.range (n+1), (if a = n - a then s a else 0) = ∑ a ∈ Finset.range (n+1), s a := by
    intro n
    obtain ⟨m, hm⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2, by omega⟩
    rcases hm with rfl | rfl
    · have e : ∀ a ∈ Finset.range (2*m+1), (if a = 2*m - a then s a else 0) = (if a = m then s a else 0) := by
        intro a ha
        have := Finset.mem_range.1 ha
        by_cases h : a = m
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      rw [Finset.sum_congr rfl e, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (by omega)), L2]
    · rw [show 2*m+1+1 = 2*(m+1) by ring, L1]
      apply Finset.sum_eq_zero
      intro a ha
      have := Finset.mem_range.1 ha
      split_ifs with h
      · exfalso; omega
      · rfl
  have key : ∀ S : Set ℕ, ∀ n : ℕ, r S n = ∑ a ∈ Finset.range (n+1), if (a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a) then 1 else 0 := by
    intro S n
    have inner : ∀ x : S, (∑' y : S, if (x ≠ y ∧ (x:ℕ) + (y:ℕ) = n) then 1 else 0) = if ((x:ℕ) ≤ n ∧ n - (x:ℕ) ∈ S ∧ (x:ℕ) ≠ n - x) then 1 else 0 := by
      intro x
      by_cases hx : (x:ℕ) ≤ n
      · by_cases hyS : n - (x:ℕ) ∈ S
        · rw [tsum_eq_single ⟨n - x, hyS⟩]
          · by_cases hxy : (x:ℕ) = n - x
            · have hx' : x = ⟨n - x, hyS⟩ := Subtype.ext hxy
              have c1 : ¬ (x ≠ ⟨n - x, hyS⟩ ∧ (x:ℕ) + ((⟨n - x, hyS⟩ : S) : ℕ) = n) := fun h => h.1 hx'
              have c2 : ¬ ((x:ℕ) ≤ n ∧ n - (x:ℕ) ∈ S ∧ (x:ℕ) ≠ n - x) := fun h => h.2.2 hxy
              rw [if_neg c1, if_neg c2]
            · have hne : x ≠ ⟨n - x, hyS⟩ := fun h => hxy (congrArg Subtype.val h)
              rw [if_pos (show x ≠ ⟨n - x, hyS⟩ ∧ (x:ℕ) + ((⟨n - x, hyS⟩ : S) : ℕ) = n from ⟨hne, by show (x:ℕ) + (n - x) = n; omega⟩), if_pos (show (x:ℕ) ≤ n ∧ n - (x:ℕ) ∈ S ∧ (x:ℕ) ≠ n - x from ⟨hx, hyS, hxy⟩)]
          · intro y hy
            rw [if_neg]
            rintro ⟨_, hsum⟩
            exact hy (Subtype.ext (by simp; omega))
        · have h0 : ∀ y : S, (if (x ≠ y ∧ (x:ℕ) + (y:ℕ) = n) then (1:ℕ) else 0) = 0 := by
            intro y
            rw [if_neg]
            rintro ⟨_, hsum⟩
            apply hyS
            have : (y:ℕ) = n - x := by omega
            rw [← this]
            exact y.2
          simp [h0, hyS]
      · have h0 : ∀ y : S, (if (x ≠ y ∧ (x:ℕ) + (y:ℕ) = n) then (1:ℕ) else 0) = 0 := by
          intro y
          rw [if_neg]
          rintro ⟨_, h⟩
          omega
        simp [h0, hx]
    rw [hr]
    simp only [inner]
    rw [tsum_subtype S (fun a : ℕ => if (a ≤ n ∧ n - a ∈ S ∧ a ≠ n - a) then (1:ℕ) else 0)]
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    · apply Finset.sum_congr rfl
      intro a ha
      have := Finset.mem_range.1 ha
      by_cases hS : a ∈ S <;> by_cases hT : n - a ∈ S <;> by_cases hne : a ≠ n - a <;> simp [Set.indicator_apply, hS, hT, hne, show a ≤ n by omega]
    · intro b hb
      have hb' : ¬ b ≤ n := fun h => hb (Finset.mem_range.2 (by omega))
      simp [Set.indicator_apply, hb']
  rw [show putnam_2003_a6_solution = True from rfl, iff_true]
  refine ⟨{n | s n = 1}, {n | s n = -1}, ?_, ?_, ?_⟩
  · ext n
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hspm n
  · ext n
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rw [h1] at h2
    norm_num at h2
  · intro n
    rw [key, key]
    simp only [Set.mem_setOf_eq]
    have pt : ∀ a ∈ Finset.range (n+1), (2:ℤ) * ((if (s a = 1 ∧ s (n-a) = 1 ∧ a ≠ n-a) then 1 else 0) - (if (s a = -1 ∧ s (n-a) = -1 ∧ a ≠ n-a) then 1 else 0)) = (s a + s (n-a)) - 2 * (if a = n-a then s a else 0) := by
      intro a _
      by_cases hab : a = n - a
      · have e : s (n-a) = s a := by rw [← hab]
        have n1 : ¬ (s a = 1 ∧ s (n-a) = 1 ∧ a ≠ n-a) := fun h => h.2.2 hab
        have n2 : ¬ (s a = -1 ∧ s (n-a) = -1 ∧ a ≠ n-a) := fun h => h.2.2 hab
        rw [if_neg n1, if_neg n2, if_pos hab, e]
        ring
      · rcases hspm a with ha | ha <;> rcases hspm (n-a) with hb | hb <;> simp [hab, ha, hb]
    have total : ∑ a ∈ Finset.range (n+1), (2:ℤ) * ((if (s a = 1 ∧ s (n-a) = 1 ∧ a ≠ n-a) then 1 else 0) - (if (s a = -1 ∧ s (n-a) = -1 ∧ a ≠ n-a) then 1 else 0)) = 0 := by
      rw [Finset.sum_congr rfl pt, Finset.sum_sub_distrib, Finset.sum_add_distrib, refl n, ← Finset.mul_sum, Z n]
      ring
    rw [← Finset.mul_sum] at total
    have h4 : ∑ a ∈ Finset.range (n+1), ((if (s a = 1 ∧ s (n-a) = 1 ∧ a ≠ n-a) then (1:ℤ) else 0) - (if (s a = -1 ∧ s (n-a) = -1 ∧ a ≠ n-a) then 1 else 0)) = 0 := by
      linarith
    rw [Finset.sum_sub_distrib] at h4
    have h5 : ∑ a ∈ Finset.range (n+1), (if (s a = 1 ∧ s (n-a) = 1 ∧ a ≠ n-a) then (1:ℤ) else 0) = ∑ a ∈ Finset.range (n+1), (if (s a = -1 ∧ s (n-a) = -1 ∧ a ≠ n-a) then (1:ℤ) else 0) := by
      linarith
    exact_mod_cast h5
