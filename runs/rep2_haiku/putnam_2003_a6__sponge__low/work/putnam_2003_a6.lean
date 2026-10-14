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
  obtain ⟨e, he0, he2, he3, hepm⟩ : ∃ e : ℕ → ℤ, e 0 = 1 ∧ (∀ m, e (2*m) = e m) ∧
      (∀ m, e (2*m+1) = - e m) ∧ (∀ n, e n = 1 ∨ e n = -1) := by
    refine ⟨fun n => (-1 : ℤ) ^ (Nat.digits 2 n).sum, by simp, ?_, ?_, fun n => neg_one_pow_eq_or ℤ _⟩
    · intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · have hk : (Nat.digits 2 (2*m)).sum = (2*m) % 2 + (Nat.digits 2 (2*m/2)).sum := by
          rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2*m)]; simp
        have h1 : 2*m % 2 = 0 := by omega
        have h2 : 2*m/2 = m := by omega
        simp only [hk, h1, h2, zero_add]
    · intro m
      have hk : (Nat.digits 2 (2*m+1)).sum = (2*m+1) % 2 + (Nat.digits 2 ((2*m+1)/2)).sum := by
        rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2*m+1)]; simp
      have h1 : (2*m+1) % 2 = 1 := by omega
      have h2 : (2*m+1)/2 = m := by omega
      simp only [hk, h1, h2]
      rw [add_comm, pow_add]; simp
  have hK : ∀ m, (∑ a ∈ Finset.range (2*m+1), e a = e m) ∧ (∑ a ∈ Finset.range (2*m+2), e a = 0) := by
    intro m
    induction m with
    | zero =>
      have h3 := he3 0
      simp only [mul_zero, zero_add] at h3 ⊢
      constructor
      · simp [he0]
      · simp [Finset.sum_range_succ, he0, h3]
    | succ k ih =>
      have c1 : 2*(k+1)+1 = (2*k+2)+1 := by ring
      have c2 : 2*k+2 = 2*(k+1) := by ring
      have hA' : ∑ a ∈ Finset.range (2*(k+1)+1), e a = e (k+1) := by
        rw [c1, Finset.sum_range_succ, ih.2, c2, he2, zero_add]
      refine ⟨hA', ?_⟩
      have c3 : 2*(k+1)+2 = (2*(k+1)+1)+1 := by ring
      rw [c3, Finset.sum_range_succ, hA', he3 (k+1)]
      ring
  have hX : ∀ n, ∑ a ∈ Finset.range (n+1), e a * (if 2*a ≠ n then (1:ℤ) else 0) = 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hterm : ∀ a, e a * (if 2*a ≠ 2*m then (1:ℤ) else 0) = e a - (if a = m then e a else 0) := by
        intro a
        by_cases h : a = m
        · subst h; simp
        · have h' : 2*a ≠ 2*m := by omega
          simp [h, h']
      have hm : m ∈ Finset.range (2*m+1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib, (hK m).1,
        Finset.sum_ite_eq', if_pos hm, sub_self]
    · have hterm : ∀ a ∈ Finset.range (2*m+1+1), e a * (if 2*a ≠ 2*m+1 then (1:ℤ) else 0) = e a := by
        intro a _
        rw [if_pos (by omega), mul_one]
      rw [Finset.sum_congr rfl hterm]
      exact (hK m).2
  have hin : ∀ n x, x ≤ n → ∑ y ∈ Finset.range (n+1), (if (x ≠ y ∧ x + y = n) then (1:ℤ) else 0)
      = (if 2*x ≠ n then (1:ℤ) else 0) := by
    intro n x hx
    have hc : ∀ y, (x ≠ y ∧ x + y = n) ↔ (y = n - x ∧ 2*x ≠ n) := by
      intro y; constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    simp only [hc]
    by_cases h : 2*x ≠ n
    · simp [h, Finset.sum_ite_eq', Finset.mem_range] <;> omega
    · have h' : 2*x = n := by omega
      simp [h']
  have hin2 : ∀ n x, x ≤ n → ∑ y ∈ Finset.range (n+1), (if (y ≠ x ∧ y + x = n) then (1:ℤ) else 0)
      = (if 2*x ≠ n then (1:ℤ) else 0) := by
    intro n x hx
    have hc : ∀ y, (y ≠ x ∧ y + x = n) ↔ (y = n - x ∧ 2*x ≠ n) := by
      intro y; constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    simp only [hc]
    by_cases h : 2*x ≠ n
    · simp [h, Finset.sum_ite_eq', Finset.mem_range] <;> omega
    · have h' : 2*x = n := by omega
      simp [h']
  have hsum : ∀ (T : Set ℕ) (f : ℕ → ℕ) (m : ℕ), (∀ x, m < x → f x = 0) →
      ∑' x : T, f x = ∑ x ∈ Finset.range (m+1), (if x ∈ T then f x else 0) := by
    intro T f m hf
    rw [tsum_subtype, tsum_eq_sum (s := Finset.range (m+1))]
    · apply Finset.sum_congr rfl
      intro x _
      simp [Set.indicator_apply]
    · intro x hx
      have hx' : m < x := by simpa using hx
      simp [Set.indicator_apply, hf x hx']
  have hconv : ∀ (S : Set ℕ) (n : ℕ), r S n = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0) := by
    intro S n
    have hinner : ∀ x y, n < y → (if (x ≠ y ∧ x + y = n) then 1 else 0) = 0 := by
      intro x y hy
      rw [if_neg]
      rintro ⟨_, h2⟩
      omega
    have hout : ∀ x, n < x → (∑' s2 : S, if (x ≠ s2 ∧ x + s2 = n) then 1 else 0) = 0 := by
      intro x hx
      rw [hsum S _ n (fun y hy => hinner x y hy)]
      apply Finset.sum_eq_zero
      intro y _
      split_ifs <;> first | rfl | (exfalso; omega)
    have hr2 : r S n = ∑' s1 : S, ∑' s2 : S, (if ((s1:ℕ) ≠ (s2:ℕ) ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0) := by
      rw [hr]
      simp only [ne_eq, Subtype.coe_inj]
    rw [hr2, hsum S (fun a => ∑' s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0)) n
      (fun x hx => hout x hx)]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S
    · rw [if_pos hx, hsum S (fun b => if (x ≠ b ∧ x + b = n) then 1 else 0) n
        (fun y hy => hinner x y hy)]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ S
      · simp [hx, hy]
      · simp [hy]
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro y _
      simp [hx]
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, ∀ x, x ∈ A ↔ e x = 1 := ⟨{x | e x = 1}, fun x => Iff.rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, ∀ x, x ∈ B ↔ e x = -1 := ⟨{x | e x = -1}, fun x => Iff.rfl⟩
  have hpt : ∀ a b n : ℕ, 2 * ((if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)
      - (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0))
      = (if (a ≠ b ∧ a + b = n) then e a + e b else 0) := by
    intro a b n
    by_cases hP : a ≠ b ∧ a + b = n
    · rcases hepm a with ha | ha <;> rcases hepm b with hb | hb <;>
        simp [hA, hB, ha, hb, hP] <;> norm_num
    · rcases hepm a with ha | ha <;> rcases hepm b with hb | hb <;>
        simp [hA, hB, ha, hb, hP] <;> norm_num
  refine ⟨fun _ => trivial, fun _ => ⟨A, B, ?_, ?_, ?_⟩⟩
  · ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true, hA, hB]
    exact hepm x
  · ext x
    simp only [Set.mem_inter_iff, hA, hB, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rw [h1] at h2
    norm_num at h2
  · intro n
    have T1 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if (a ≠ b ∧ a + b = n) then e a else 0)
        = ∑ a ∈ Finset.range (n+1), e a * (if 2*a ≠ n then (1:ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : a ≤ n := by simp at ha; omega
      rw [← hin n a ha', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    have T2 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if (a ≠ b ∧ a + b = n) then e b else 0)
        = ∑ b ∈ Finset.range (n+1), e b * (if 2*b ≠ n then (1:ℤ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ n := by simp at hb; omega
      rw [← hin2 n b hb', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    have hmain : 2 * (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)
        - ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)) = 0 := by
      calc 2 * (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)
            - ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0))
          = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            2 * ((if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)
            - (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then (1:ℤ) else 0)) := by
            simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
        _ = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if (a ≠ b ∧ a + b = n) then e a + e b else 0) :=
            Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b n))
        _ = (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if (a ≠ b ∧ a + b = n) then e a else 0))
            + ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if (a ≠ b ∧ a + b = n) then e b else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            split_ifs <;> simp
        _ = (∑ a ∈ Finset.range (n+1), e a * (if 2*a ≠ n then (1:ℤ) else 0))
            + ∑ b ∈ Finset.range (n+1), e b * (if 2*b ≠ n then (1:ℤ) else 0) := by
            rw [T1, T2]
        _ = 0 := by rw [hX n, add_zero]
    rw [hconv A n, hconv B n, ← Nat.cast_inj (R := ℤ)]
    push_cast
    linarith [hmain]
