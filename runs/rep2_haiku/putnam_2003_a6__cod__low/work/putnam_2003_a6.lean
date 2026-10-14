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
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℕ, ∀ n, s n = (Nat.digits 2 n).sum % 2 := ⟨_, fun _ => rfl⟩
  have hs_lt : ∀ n, s n < 2 := fun n => by rw [hs_def]; omega
  have key : ∀ n, s n = (n % 2 + s (n / 2)) % 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs_def]
    · rw [hs_def, hs_def (n / 2), Nat.digits_def' (by norm_num) hn, List.sum_cons]
      omega
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, ∀ a, e a = if s a = 0 then 1 else -1 := ⟨_, fun _ => rfl⟩
  have e_even : ∀ k, e (2 * k) = e k := by
    intro k
    have h := key (2 * k)
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2] at h
    have := hs_lt k
    rw [he, he]
    split_ifs <;> omega
  have e_odd : ∀ k, e (2 * k + 1) = - e k := by
    intro k
    have h := key (2 * k + 1)
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h1, h2] at h
    have := hs_lt k
    rw [he, he]
    split_ifs <;> omega
  have e_pair : ∀ k, e (2 * k) + e (2 * k + 1) = 0 := by
    intro k; rw [e_even, e_odd]; ring
  have hT : ∀ m, ∑ a ∈ Finset.range (2 * m), e a = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have := e_pair m
      linarith
  have G : ∀ n, ∑ a ∈ Finset.range (n + 1), (if 2 * a ≠ n then e a else 0) = 0 := by
    intro n
    have split : ∑ a ∈ Finset.range (n + 1), (if 2 * a ≠ n then e a else 0)
        = ∑ a ∈ Finset.range (n + 1), e a - ∑ a ∈ Finset.range (n + 1), (if 2 * a = n then e a else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : 2 * a = n <;> simp [h]
    rw [split]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h2 : ∑ a ∈ Finset.range (2 * m + 1), (if 2 * a = 2 * m then e a else 0) = e m := by
        rw [Finset.sum_eq_single m]
        · simp
        · intro b _ hb
          rw [if_neg (by omega)]
        · intro hm
          exfalso; apply hm; simp; omega
      rw [h2, Finset.sum_range_succ, hT m, e_even m]
      ring
    · have h2 : ∑ a ∈ Finset.range (2 * m + 1 + 1), (if 2 * a = 2 * m + 1 then e a else 0) = 0 :=
        Finset.sum_eq_zero (fun a _ => if_neg (by omega))
      rw [h2, sub_zero, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hT (m + 1)]
  have hsym : ∀ n, ∑ k ∈ Finset.range (n + 1), (if 2 * k ≠ n then e (n - k) else 0)
      = ∑ k ∈ Finset.range (n + 1), (if 2 * k ≠ n then e k else 0) := by
    intro n
    have := Finset.sum_range_reflect (fun k => if 2 * k ≠ n then e k else 0) (n + 1)
    rw [← this]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Nat.add_sub_cancel]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  have hr' : ∀ S : Set ℕ, ∀ n, r S n = ∑ k ∈ Finset.range (n + 1),
      (if (k ∈ S ∧ n - k ∈ S ∧ k ≠ n - k) then 1 else 0) := by
    have hsub : ∀ (S : Set ℕ) (f : ℕ → ℕ) (T : Finset ℕ), (∀ x, x ∉ T → f x = 0) →
        ∑' x : S, f x = ∑ x ∈ T, if x ∈ S then f x else 0 := by
      intro S f T hf
      rw [tsum_subtype, tsum_eq_sum (s := T)]
      · apply Finset.sum_congr rfl
        intro x _
        simp [Set.indicator_apply]
      · intro x hx
        simp [Set.indicator_apply, hf x hx]
    intro S n
    rw [hr]
    simp only [ne_eq, Subtype.ext_iff]
    rw [hsub S (fun k => ∑' s2 : S, if (k ≠ (s2:ℕ) ∧ k + (s2:ℕ) = n) then 1 else 0) (Finset.range (n+1))]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hsub S (fun j => if (k ≠ j ∧ k + j = n) then 1 else 0) (Finset.range (n+1))]
      · rw [Finset.sum_eq_single (n - k)]
        · have hkn : k + (n - k) = n := by omega
          by_cases a : k ∈ S <;> by_cases b : n - k ∈ S <;> by_cases c : k ≠ n - k <;>
            simp [a, b, c, hkn]
        · intro y hy hyne
          simp only [Finset.mem_range] at hy
          split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
        · intro h
          exfalso; apply h; simp
      · intro x hx
        simp only [Finset.mem_range, not_lt] at hx
        split_ifs with h <;> first | rfl | (exfalso; omega)
    · intro x hx
      simp only [Finset.mem_range, not_lt] at hx
      refine (tsum_congr (g := fun _ : S => (0:ℕ)) (fun s2 => ?_)).trans tsum_zero
      split_ifs with h <;> first | rfl | (exfalso; omega)
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨{a | s a = 0}, {a | s a = 1}, ?_, ?_, ?_⟩
    · ext a
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have := hs_lt a
      omega
    · ext a
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; omega
    · intro n
      rw [hr', hr']
      simp only [Set.mem_setOf_eq]
      apply Nat.cast_injective (R := ℤ)
      push_cast
      apply mul_left_cancel₀ (two_ne_zero : (2:ℤ) ≠ 0)
      rw [Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
      have pw : ∀ k ∈ Finset.range (n + 1),
          2 * (if (s k = 0 ∧ s (n - k) = 0 ∧ k ≠ n - k) then (1:ℤ) else 0)
            - 2 * (if (s k = 1 ∧ s (n - k) = 1 ∧ k ≠ n - k) then (1:ℤ) else 0)
          = (if 2 * k ≠ n then e k else 0) + (if 2 * k ≠ n then e (n - k) else 0) := by
        intro k hk
        simp only [Finset.mem_range] at hk
        have h1 := hs_lt k
        have h2 := hs_lt (n - k)
        rw [he k, he (n - k)]
        split_ifs <;> omega
      rw [Finset.sum_congr rfl pw, Finset.sum_add_distrib, hsym n, G n]
      simp
