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
  -- Thue-Morse style parity function s (binary digit sum)
  obtain ⟨s, h0, h1⟩ : ∃ s : ℕ → ℕ, (∀ n, s (2*n) = s n) ∧ (∀ n, s (2*n+1) = s n + 1) := by
    refine ⟨fun n => (Nat.digits 2 n).sum, fun n => ?_, fun n => ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · show (Nat.digits 2 (2*n)).sum = (Nat.digits 2 n).sum
        rw [Nat.digits_def' (by norm_num) (by omega : 0 < 2*n)]
        have h2 : 2*n % 2 = 0 := by omega
        have h3 : 2*n/2 = n := by omega
        rw [h2, h3]; simp
    · show (Nat.digits 2 (2*n+1)).sum = (Nat.digits 2 n).sum + 1
      rw [Nat.digits_def' (by norm_num) (by omega : 0 < 2*n+1)]
      have h2 : (2*n+1) % 2 = 1 := by omega
      have h3 : (2*n+1)/2 = n := by omega
      rw [h2, h3]; simp only [List.sum_cons]; omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℤ, ∀ a, ε a = if Even (s a) then 1 else -1 :=
    ⟨fun a => if Even (s a) then 1 else -1, fun a => rfl⟩
  have hεe : ∀ m, ε (2*m) = ε m := by
    intro m; rw [hε, hε, h0]
  have hεo : ∀ m, ε (2*m+1) = - ε m := by
    intro m; rw [hε, hε, h1]
    by_cases h : Even (s m) <;> simp [h, Nat.even_add_one]
  have hsum2 : ∀ m, ∑ a ∈ Finset.range (2*m), ε a = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = 2*k+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        hεo, hεe]
      ring
  have hsumodd : ∀ m, ∑ a ∈ Finset.range (2*m+1), ε a = ε m := by
    intro m
    rw [Finset.sum_range_succ, hsum2, zero_add, hεe]
  have key : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hpt : ∀ a, (if a ≠ 2*m - a then ε a else 0)
          = ε a - (if a = 2*m - a then ε a else 0) := by
        intro a
        by_cases h : a = 2*m - a
        · rw [if_neg (fun h' => h' h), if_pos h, sub_self]
        · rw [if_pos h, if_neg h, sub_zero]
      have hm : ∑ a ∈ Finset.range (2*m+1), (if a = 2*m - a then ε a else 0) = ε m := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (show m = 2*m - m by omega)]
        · intro b hb hbm
          rw [Finset.mem_range] at hb
          rw [if_neg (show ¬ (b = 2*m - b) by omega)]
        · intro h; exact absurd (Finset.mem_range.2 (show m < 2*m+1 by omega)) h
      rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib, hsumodd, hm, sub_self]
    · have hpt : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then ε a else 0) = ε a := by
        intro a ha
        rw [Finset.mem_range] at ha
        rw [if_pos (show a ≠ 2*m+1 - a by omega)]
      rw [Finset.sum_congr rfl hpt, show 2*m+1+1 = 2*(m+1) by ring, hsum2]
  have pw : ∀ a b : ℕ, 2 * ((if (Even (s a) ∧ Even (s b) ∧ a ≠ b) then (1:ℤ) else 0)
      - (if (¬ Even (s a) ∧ ¬ Even (s b) ∧ a ≠ b) then (1:ℤ) else 0))
      = if a ≠ b then ε a + ε b else 0 := by
    intro a b
    rw [hε a, hε b]
    by_cases hab : a = b <;> by_cases ha : Even (s a) <;> by_cases hb : Even (s b) <;>
      simp [hab, ha, hb]
  -- r as a finite sum
  have hr2 : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S,
      (if ((s1:ℕ) ≠ (s2:ℕ) ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ) := by
    intro S n
    rw [hr]
    refine tsum_congr fun s1 => tsum_congr fun s2 => ?_
    simp only [ne_eq, Subtype.ext_iff]
  have finN : ∀ (S : Set ℕ) (n : ℕ), r S n = ∑ a ∈ Finset.range (n+1),
      ∑ b ∈ Finset.range (n+1), (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0) := by
    intro S n
    have hF0 : ∀ a b, (n < a ∨ n < b) →
        (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) = 0 := by
      intro a b h
      apply if_neg
      rintro ⟨_, _, _, h4⟩
      omega
    have hstep : (∑' s1 : S, ∑' s2 : S,
        (if ((s1:ℕ) ≠ (s2:ℕ) ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ))
        = ∑' a : ℕ, ∑' b : ℕ, (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) := by
      calc (∑' s1 : S, ∑' s2 : S,
            (if ((s1:ℕ) ≠ (s2:ℕ) ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ))
          = ∑' s1 : S, ∑' b : ℕ, S.indicator
              (fun b => (if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0 : ℕ)) b :=
            tsum_congr fun s1 => tsum_subtype S
              (fun b => (if ((s1:ℕ) ≠ b ∧ (s1:ℕ) + b = n) then 1 else 0 : ℕ))
        _ = ∑' a : ℕ, S.indicator
              (fun a => ∑' b : ℕ, S.indicator
                (fun b => (if (a ≠ b ∧ a + b = n) then 1 else 0 : ℕ)) b) a :=
            tsum_subtype S (fun a => ∑' b : ℕ, S.indicator
                (fun b => (if (a ≠ b ∧ a + b = n) then 1 else 0 : ℕ)) b)
        _ = ∑' a : ℕ, ∑' b : ℕ, (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) := by
            refine tsum_congr fun a => ?_
            by_cases ha : a ∈ S
            · simp only [Set.indicator_of_mem ha]
              refine tsum_congr fun b => ?_
              by_cases hb : b ∈ S
              · simp [ha, hb]
              · simp [hb]
            · simp [ha]
    have hout : ∀ a ∉ Finset.range (n+1), ∑' b : ℕ,
        (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) = 0 := by
      intro a ha
      have : ∀ b, (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) = 0 :=
        fun b => hF0 a b (Or.inl (by simp at ha; omega))
      simp [this]
    have hin : ∀ a, ∑' b : ℕ, (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ)
        = ∑ b ∈ Finset.range (n+1), (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) :=
      fun a => tsum_eq_sum (fun b hb => hF0 a b (Or.inr (by simp at hb; omega)))
    rw [hr2, hstep, tsum_eq_sum (fun a ha => hout a ha)]
    exact Finset.sum_congr rfl (fun a _ => hin a)
  have finZ : ∀ (S : Set ℕ) (n : ℕ), (r S n : ℤ) = ∑ a ∈ Finset.range (n+1),
      ∑ b ∈ Finset.range (n+1), (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0) := by
    intro S n
    rw [finN]
    push_cast
    rfl
  have hrefl : ∀ n, ∑ j ∈ Finset.range (n+1), (if j ≠ n - j then ε (n - j) else 0)
      = ∑ j ∈ Finset.range (n+1), (if j ≠ n - j then ε j else 0) := by
    intro n
    rw [← Finset.sum_range_reflect (fun j => if j ≠ n - j then ε j else 0) (n+1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have e1 : n + 1 - 1 - j = n - j := by omega
    have e2 : n - (n - j) = j := by omega
    simp only [e1, e2]
    split_ifs <;> first | rfl | omega
  have hcol : ∀ (S : Set ℕ) (n : ℕ), ∑ a ∈ Finset.range (n+1),
      ∑ b ∈ Finset.range (n+1), (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)
      = ∑ a ∈ Finset.range (n+1), (if (a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a) then (1:ℤ) else 0) := by
    intro S n
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.sum_eq_single (n - a)]
    · have : a + (n - a) = n := by omega
      simp [this]
    · intro b hb hbne
      rw [Finset.mem_range] at hb
      apply if_neg
      rintro ⟨_, _, _, h4⟩
      omega
    · intro h
      exact absurd (Finset.mem_range.2 (show n - a < n + 1 by omega)) h
  have hU : ({x : ℕ | Even (s x)} ∪ {x : ℕ | ¬ Even (s x)}) = (Set.univ : Set ℕ) :=
    Set.eq_univ_of_forall (fun x => (em (Even (s x))).elim (fun h => Or.inl h) (fun h => Or.inr h))
  have hI : ({x : ℕ | Even (s x)} ∩ {x : ℕ | ¬ Even (s x)}) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    tauto
  have hEq : ∀ n : ℕ, r {x : ℕ | Even (s x)} n = r {x : ℕ | ¬ Even (s x)} n := by
    intro n
    have hAfin : (r {x : ℕ | Even (s x)} n : ℤ) = ∑ a ∈ Finset.range (n+1),
        (if (Even (s a) ∧ Even (s (n - a)) ∧ a ≠ n - a) then (1:ℤ) else 0) := by
      rw [finZ, hcol]
      exact Finset.sum_congr rfl (fun a _ => by simp)
    have hBfin : (r {x : ℕ | ¬ Even (s x)} n : ℤ) = ∑ a ∈ Finset.range (n+1),
        (if (¬ Even (s a) ∧ ¬ Even (s (n - a)) ∧ a ≠ n - a) then (1:ℤ) else 0) := by
      rw [finZ, hcol]
      exact Finset.sum_congr rfl (fun a _ => by simp)
    have hZ : (r {x : ℕ | Even (s x)} n : ℤ) = r {x : ℕ | ¬ Even (s x)} n := by
      rw [hAfin, hBfin, ← sub_eq_zero]
      apply mul_left_cancel₀ (show (2:ℤ) ≠ 0 by norm_num)
      rw [mul_zero, ← Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun a _ => pw a (n - a))]
      have hsplit : ∀ a, (if a ≠ n - a then ε a + ε (n - a) else 0)
          = (if a ≠ n - a then ε a else 0) + (if a ≠ n - a then ε (n - a) else 0) :=
        fun a => by split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib, hrefl n, key n, add_zero]
    exact_mod_cast hZ
  exact ⟨fun _ => trivial, fun _ => ⟨_, _, hU, hI, hEq⟩⟩
