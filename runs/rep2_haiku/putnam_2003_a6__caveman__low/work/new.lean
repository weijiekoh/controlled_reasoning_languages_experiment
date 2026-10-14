import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution
:= by
  classical
  obtain ⟨tm, htm⟩ : ∃ tm : ℕ → ℤ, ∀ n, tm n = if (Nat.digits 2 n).sum % 2 = 0 then 1 else -1 :=
    ⟨_, fun n => rfl⟩
  have hd0 : ∀ m, (Nat.digits 2 (2*m)).sum = (Nat.digits 2 m).sum := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Nat.digits_def' (by norm_num) (by omega)]
      rw [show 2*m % 2 = 0 by omega, show 2*m / 2 = m by omega]
      simp
  have hd1 : ∀ m, (Nat.digits 2 (2*m+1)).sum = (Nat.digits 2 m).sum + 1 := by
    intro m
    rw [Nat.digits_def' (by norm_num) (by omega)]
    rw [show (2*m+1) % 2 = 1 by omega, show (2*m+1) / 2 = m by omega]
    simp only [List.sum_cons]
    omega
  have he : ∀ m, tm (2*m) = tm m := by
    intro m; rw [htm, htm, hd0]
  have ho : ∀ m, tm (2*m+1) = -tm m := by
    intro m; rw [htm, htm, hd1]; split_ifs <;> omega
  have hpm : ∀ n, tm n = 1 ∨ tm n = -1 := by
    intro n; rw [htm]; split_ifs <;> simp
  have hA : ∀ m, ∑ a ∈ Finset.range (2*m+1), tm a = tm m ∧
      ∑ a ∈ Finset.range (2*m+1+1), tm a = 0 := by
    intro m
    induction m with
    | zero =>
      have h2 : tm 1 = -tm 0 := by simpa using ho 0
      simp [Finset.sum_range_succ, h2]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have he' : tm (2*k+2) = tm (k+1) := by
        have := he (k+1); rw [show 2*(k+1) = 2*k+2 by ring] at this; exact this
      have ho' : tm (2*k+3) = -tm (k+1) := by
        have := ho (k+1); rw [show 2*(k+1)+1 = 2*k+3 by ring] at this; exact this
      have c1 : ∑ a ∈ Finset.range (2*(k+1)+1), tm a = tm (k+1) := by
        rw [show 2*(k+1)+1 = (2*k+1+1)+1 by ring, Finset.sum_range_succ, ih2,
          show 2*k+1+1 = 2*k+2 by ring, he']
        ring
      refine ⟨c1, ?_⟩
      rw [show 2*(k+1)+1+1 = (2*(k+1)+1)+1 by ring, Finset.sum_range_succ, c1,
        show 2*(k+1)+1 = 2*k+3 by ring, ho']
      ring
  have R : ∀ k, ∑ a ∈ Finset.range (k+1), tm (k - a) = ∑ a ∈ Finset.range (k+1), tm a := by
    intro k
    have := Finset.sum_range_reflect tm (k+1)
    simp only [Nat.add_sub_cancel] at this
    exact this
  have L : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then tm a + tm (n - a) else 0) = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have e1 : ∑ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then tm a + tm (2*m - a) else 0)
          = ∑ a ∈ Finset.range (2*m+1), (tm a + tm (2*m - a))
            - ∑ a ∈ Finset.range (2*m+1), (if a = m then 2 * tm m else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_range] at ha
        by_cases h : a = m
        · have h2 : 2*m - a = m := by omega
          rw [if_neg (show ¬ (a ≠ 2*m - a) by omega), if_pos h, h2, h]
          ring
        · rw [if_pos (show a ≠ 2*m - a by omega), if_neg h, sub_zero]
      rw [e1, Finset.sum_add_distrib, R (2*m), (hA m).1,
        Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega : m < 2*m+1))]
      ring
    · have e2 : ∑ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then tm a + tm (2*m+1 - a) else 0)
          = ∑ a ∈ Finset.range (2*m+1+1), (tm a + tm (2*m+1 - a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_range] at ha
        rw [if_pos (show a ≠ 2*m+1 - a by omega)]
      rw [e2, Finset.sum_add_distrib, R (2*m+1), (hA m).2]
      ring
  have hr_eq : ∀ (S : Set ℕ) (n : ℕ), r S n =
      ∑ a ∈ Finset.range (n+1), (if a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a then 1 else 0) := by
    intro S n
    rw [hr]
    have inner : ∀ s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ)
        = ∑' b : ℕ, S.indicator (fun b => if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0) b := by
      intro s1
      rw [← tsum_subtype S (fun b => if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0)]
      apply tsum_congr
      intro s2
      simp [Subtype.ext_iff]
    simp only [inner]
    rw [tsum_subtype S (fun a => ∑' b, S.indicator (fun b => if (a ≠ b ∧ a + b = n) then 1 else 0) b)]
    have hz0 : ∀ a, n < a → ∑' b, S.indicator (fun b => if (a ≠ b ∧ a + b = n) then 1 else 0) b = 0 := by
      intro a ha
      have : ∀ b, S.indicator (fun b => if (a ≠ b ∧ a + b = n) then (1:ℕ) else 0) b = 0 := by
        intro b
        simp only [Set.indicator_apply]
        split_ifs <;> first | rfl | omega
      simp [this]
    have hval : ∀ a, a ≤ n → ∑' b, S.indicator (fun b => if (a ≠ b ∧ a + b = n) then 1 else 0) b
        = if (n - a ∈ S ∧ a ≠ n - a) then 1 else 0 := by
      intro a ha
      rw [tsum_eq_single (n - a)]
      · simp only [Set.indicator_apply]
        have hs : a + (n - a) = n := by omega
        by_cases h1 : n - a ∈ S <;> by_cases h2 : a ≠ n - a <;> simp [h1, h2, hs]
      · intro b hb
        simp only [Set.indicator_apply]
        split_ifs <;> first | rfl | omega
    rw [tsum_eq_sum (s := Finset.range (n+1)) ?_]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_range] at ha
      rw [Set.indicator_apply, hval a (by omega)]
      by_cases h1 : a ∈ S <;> by_cases h2 : n - a ∈ S <;> by_cases h3 : a ≠ n - a <;> simp [h1, h2, h3]
    · intro a ha
      rw [Finset.mem_range] at ha
      rw [Set.indicator_apply]
      split_ifs
      · exact hz0 a (by omega)
      · rfl
  have key : ∀ n a : ℕ, 2 * ((if (a ∈ {x : ℕ | tm x = 1} ∧ n - a ∈ {x : ℕ | tm x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)
      - (if (a ∈ {x : ℕ | tm x = -1} ∧ n - a ∈ {x : ℕ | tm x = -1} ∧ a ≠ n - a) then (1:ℤ) else 0))
      = if a ≠ n - a then tm a + tm (n - a) else 0 := by
    intro n a
    have h1 := hpm a
    have h2 := hpm (n - a)
    simp only [Set.mem_setOf_eq]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;>
      by_cases hne : a ≠ n - a <;> simp [hne]
  refine ⟨fun _ => trivial, fun _ => ⟨{x : ℕ | tm x = 1}, {x : ℕ | tm x = -1}, ?_, ?_, ?_⟩⟩
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases hpm x with h | h <;> simp [h]
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1; rw [h1]; norm_num
  · intro n
    have hz : (r {x : ℕ | tm x = 1} n : ℤ) - (r {x : ℕ | tm x = -1} n : ℤ) = 0 := by
      rw [hr_eq, hr_eq]
      push_cast
      rw [← Finset.sum_sub_distrib]
      have h3 : 2 * (∑ a ∈ Finset.range (n+1), ((if (a ∈ {x : ℕ | tm x = 1} ∧ n - a ∈ {x : ℕ | tm x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)
          - (if (a ∈ {x : ℕ | tm x = -1} ∧ n - a ∈ {x : ℕ | tm x = -1} ∧ a ≠ n - a) then (1:ℤ) else 0)))
          = 0 := by
        rw [Finset.mul_sum]
        rw [show (∑ a ∈ Finset.range (n+1), 2 * (((if (a ∈ {x : ℕ | tm x = 1} ∧ n - a ∈ {x : ℕ | tm x = 1} ∧ a ≠ n - a) then (1:ℤ) else 0)
          - (if (a ∈ {x : ℕ | tm x = -1} ∧ n - a ∈ {x : ℕ | tm x = -1} ∧ a ≠ n - a) then (1:ℤ) else 0))))
          = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then tm a + tm (n - a) else 0) from
          Finset.sum_congr rfl (fun a _ => key n a)]
        exact L n
      omega
    have : ((r {x : ℕ | tm x = 1} n : ℕ) : ℤ) = ((r {x : ℕ | tm x = -1} n : ℕ) : ℤ) := by linarith
    exact_mod_cast this
