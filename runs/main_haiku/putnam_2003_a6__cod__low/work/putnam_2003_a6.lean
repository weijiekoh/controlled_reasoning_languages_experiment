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
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun a => (Nat.digits 2 a).sum % 2 := ⟨_, rfl⟩
  have t_lt : ∀ a, t a < 2 := by
    intro a; rw [ht]; exact Nat.mod_lt _ (by norm_num)
  have t_even : ∀ m, t (2*m) = t m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [ht]; dsimp only
      rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2*m)]
      have h1 : 2*m % 2 = 0 := by omega
      have h2 : 2*m / 2 = m := by omega
      rw [h1, h2]; simp
  have t_odd : ∀ m, t (2*m+1) = (t m + 1) % 2 := by
    intro m
    rw [ht]; dsimp only
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2*m+1)]
    have h1 : (2*m+1) % 2 = 1 := by omega
    have h2 : (2*m+1) / 2 = m := by omega
    rw [h1, h2]
    simp only [List.sum_cons]
    omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℤ, ε = fun a => if t a = 0 then 1 else -1 := ⟨_, rfl⟩
  have eps_even : ∀ m, ε (2*m) = ε m := by
    intro m; rw [hε]; simp only [t_even]
  have eps_pair : ∀ k, ∑ a ∈ Finset.range (2*k), ε a = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = 2*k+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [hε]
      simp only [t_even, t_odd]
      have := t_lt k
      split_ifs <;> omega
  have eps_sum : ∀ m, ∑ a ∈ Finset.range (2*m+1), ε a = ε m := by
    intro m; rw [Finset.sum_range_succ, eps_pair, zero_add, eps_even]
  have core : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have h : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then ε a else 0)
          = ε a - (if a = m then ε a else 0) := by
        intro a ha
        have ha' := Finset.mem_range.mp ha
        by_cases h1 : a = m
        · have h2 : ¬ (a ≠ 2*m - a) := by omega
          rw [if_neg h2, if_pos h1]; ring
        · have h2 : a ≠ 2*m - a := by omega
          rw [if_pos h2, if_neg h1]; ring
      rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, eps_sum,
        Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      ring
    · have h : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then ε a else 0) = ε a := by
        intro a _
        rw [if_pos (by omega)]
      rw [Finset.sum_congr rfl h, show 2*m+1+1 = 2*(m+1) by ring, eps_pair]
  have red : ∀ S : Set ℕ, ∀ n, r S n = ∑ a ∈ Finset.range (n+1),
      (if (a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a) then 1 else 0) := by
    intro S n
    have hsub : ∀ s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ)
        = ∑' b : ℕ, S.indicator (fun b => if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0) b := by
      intro s1
      rw [← tsum_subtype S (fun b => if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0)]
      apply tsum_congr; intro s2; simp only [ne_eq, Subtype.ext_iff]
    have hz2 : ∀ a b, n < b → S.indicator (fun b => if (a ≠ b ∧ a + b = n) then (1:ℕ) else 0) b = 0 := by
      intro a b hb
      rw [Set.indicator_apply]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
    rw [hr]
    simp only [hsub]
    refine (tsum_subtype S (fun a : ℕ => ∑' b : ℕ, S.indicator (fun b => if ((a:ℕ) ≠ b ∧ (a:ℕ) + b = n) then (1:ℕ) else 0) b)).trans ?_
    rw [tsum_eq_sum (s := Finset.range (n+1)) ?_]
    · apply Finset.sum_congr rfl
      intro a ha
      try dsimp only
      have ha' := Finset.mem_range.mp ha
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS]
        rw [tsum_eq_sum (s := Finset.range (n+1)) (fun b hb => hz2 a b (by simp at hb; omega))]
        rw [Finset.sum_eq_single (n-a)]
        · by_cases hna : n - a ∈ S <;> by_cases hne : a ≠ n - a <;>
            simp [haS, hna, hne, show a + (n-a) = n by omega]
        · intro b hb hbne
          rw [Set.indicator_apply]
          split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
        · intro h; exfalso; apply h; rw [Finset.mem_range]; omega
      · rw [Set.indicator_of_notMem haS, if_neg (fun h => haS h.1)]
    · intro a ha
      have ha' : n < a := by simp at ha; omega
      have hin : ∀ b, S.indicator (fun b => if (a ≠ b ∧ a + b = n) then (1:ℕ) else 0) b = 0 := by
        intro b
        rw [Set.indicator_apply]
        split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
      try dsimp only
      rw [Set.indicator_apply]
      split_ifs
      · simp only [hin, tsum_zero]
      · rfl
  have hpt_all : ∀ n, ∑ a ∈ Finset.range (n+1), ((if (a ∈ {x | t x = 0} ∧ n - a ∈ {x | t x = 0} ∧ a ≠ n - a) then (1:ℤ) else 0)
      - (if (a ∈ {x | t x = 1} ∧ n - a ∈ {x | t x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)) = 0 := by
    intro n
    have hpt : ∀ a ∈ Finset.range (n+1),
        2 * ((if (a ∈ {x | t x = 0} ∧ n - a ∈ {x | t x = 0} ∧ a ≠ n - a) then (1:ℤ) else 0)
          - (if (a ∈ {x | t x = 1} ∧ n - a ∈ {x | t x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0))
        = (if a ≠ n - a then ε a else 0) + (if a ≠ n - a then ε (n - a) else 0) := by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      simp only [Set.mem_setOf_eq, hε]
      have := t_lt a
      have := t_lt (n - a)
      split_ifs <;> omega
    have hrefl : ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε (n - a) else 0)
        = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) := by
      rw [← Finset.sum_range_reflect (fun a => if a ≠ n - a then ε a else 0) (n+1)]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      have e1 : n + 1 - 1 - a = n - a := by omega
      have e2 : n - (n - a) = a := by omega
      simp only [e1, e2]
      exact if_congr ⟨fun h h2 => h h2.symm, fun h h2 => h h2.symm⟩ rfl rfl
    have h2 : 2 * ∑ a ∈ Finset.range (n+1), ((if (a ∈ {x | t x = 0} ∧ n - a ∈ {x | t x = 0} ∧ a ≠ n - a) then (1:ℤ) else 0)
      - (if (a ∈ {x | t x = 1} ∧ n - a ∈ {x | t x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0))
        = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) + ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε (n - a) else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hpt
    rw [hrefl, core n] at h2
    linarith
  have hfin : ∀ n, ∑ a ∈ Finset.range (n+1), ((if (a ∈ {x | t x = 0} ∧ n - a ∈ {x | t x = 0} ∧ a ≠ n - a) then (1:ℤ) else 0)
      - (if (a ∈ {x | t x = 1} ∧ n - a ∈ {x | t x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)) = 0 := hpt_all
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  refine ⟨{x | t x = 0}, {x | t x = 1}, ?_, ?_, ?_⟩
  · ext x
    have := t_lt x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    omega
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    omega
  · intro n
    rw [red, red]
    have hT := hfin n
    rw [Finset.sum_sub_distrib] at hT
    have h3 : ∑ a ∈ Finset.range (n+1), ((if (a ∈ {x | t x = 0} ∧ n - a ∈ {x | t x = 0} ∧ a ≠ n - a) then (1:ℤ) else 0))
        = ∑ a ∈ Finset.range (n+1), ((if (a ∈ {x | t x = 1} ∧ n - a ∈ {x | t x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)) :=
      sub_eq_zero.mp hT
    apply Nat.cast_injective (R := ℤ)
    push_cast
    convert h3
