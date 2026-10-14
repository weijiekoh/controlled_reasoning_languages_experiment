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
  have L1 : ∀ (n : ℕ) (S : Set ℕ) (G : ℕ → ℕ → ℕ), (∀ a b, (n < a ∨ n < b) → G a b = 0) →
      ∑' x : S, ∑' y : S, G x y = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        if a ∈ S then (if b ∈ S then G a b else 0) else 0 := by
    intro n S G hG
    rw [tsum_subtype S (fun x => ∑' y : S, G x y)]
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    · apply Finset.sum_congr rfl
      intro a ha
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS, tsum_subtype S (G a)]
        rw [tsum_eq_sum (s := Finset.range (n+1))]
        · simp only [haS, if_true]
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hbS : b ∈ S
          · rw [Set.indicator_of_mem hbS]; simp [hbS]
          · rw [Set.indicator_of_notMem hbS]; simp [hbS]
        · intro b hb
          by_cases hbS : b ∈ S
          · rw [Set.indicator_of_mem hbS]
            have : n < b := by simp at hb; omega
            simp [hG a b (Or.inr this)]
          · rw [Set.indicator_of_notMem hbS]
      · rw [Set.indicator_of_notMem haS]
        simp [haS]
    · intro a ha
      have : n < a := by simp at ha; omega
      have hz : ∀ b, G a b = 0 := fun b => hG a b (Or.inl this)
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS]
        simp [hz]
      · rw [Set.indicator_of_notMem haS]
  obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p : ℕ → ℕ, (∀ n, p n ≤ 1) ∧ (∀ k, p (2*k) = p k) ∧
      (∀ k, p (2*k+1) + p (2*k) = 1) := by
    have hd : ∀ n, 0 < n → (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n/2)).sum := by
      intro n hn
      rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]
    refine ⟨fun n => (Nat.digits 2 n).sum % 2, ?_, ?_, ?_⟩
    · intro n; simp only; omega
    · intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h1 := hd (2*k) (by omega)
        have h2 : 2*k/2 = k := by omega
        rw [h2] at h1
        simp only
        rw [h1]; omega
    · intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h1 := hd (2*k+1) (by omega)
        have h2 : (2*k+1)/2 = k := by omega
        have h3 := hd (2*k) (by omega)
        have h4 : 2*k/2 = k := by omega
        rw [h2] at h1
        rw [h4] at h3
        simp only
        rw [h1, h3]; omega
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, ∀ a, e a = 1 - 2 * (p a : ℤ) := ⟨_, fun a => rfl⟩
  have eev : ∀ k, e (2*k) = e k := by intro k; rw [he, he, hp2]
  have eod : ∀ k, e (2*k+1) = - e (2*k) := by
    intro k; rw [he, he]; have := hp3 k; omega
  have T : ∀ m, ∑ a ∈ Finset.range (2*m), e a = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, eod]
      ring
  have hsumOdd : ∀ m, ∑ a ∈ Finset.range (2*m+1), e a = e m := by
    intro m; rw [Finset.sum_range_succ, T, zero_add, eev]
  have hFinal : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then (1:ℤ) else 0) * e a = 0 := by
    intro n
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then (1:ℤ) else 0) * e a
          = e a - (if a = m then e a else 0) := by
        intro a ha
        have ha' : a ≤ 2*m := by simp at ha; omega
        by_cases h : a = m
        · rw [if_pos h, if_neg (by omega : ¬ (a ≠ 2*m - a))]; simp
        · rw [if_neg h, if_pos (by omega : a ≠ 2*m - a)]; simp
      rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, hsumOdd]
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      rw [if_pos (by omega : m < 2*m+1)]; ring
    · have h : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then (1:ℤ) else 0) * e a
          = e a := by
        intro a ha
        have : a ≠ 2*m+1 - a := by simp at ha; omega
        simp [this]
      rw [Finset.sum_congr rfl h, show 2*m+1+1 = 2*(m+1) by ring, T]
  have hinner : ∀ n a, a ≤ n → ∑ b ∈ Finset.range (n+1),
      (if a ≠ b ∧ a + b = n then (1:ℤ) else 0) = if a ≠ n - a then 1 else 0 := by
    intro n a ha
    rw [Finset.sum_eq_single (n-a)]
    · by_cases h : a ≠ n - a
      · rw [if_pos h, if_pos ⟨h, by omega⟩]
      · rw [if_neg h, if_neg (fun hh => h hh.1)]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨_, hab⟩
      apply hb; omega
    · intro hn
      exfalso; apply hn; rw [Finset.mem_range]; omega
  have gcomm : ∀ n x y : ℕ, (if y ≠ x ∧ y + x = n then (1:ℤ) else 0)
      = if x ≠ y ∧ x + y = n then 1 else 0 := by
    intro n x y
    have : (y ≠ x ∧ y + x = n) ↔ (x ≠ y ∧ x + y = n) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨fun h => h1 h.symm, by omega⟩
    simp only [this]
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, ∀ x, x ∈ A ↔ p x = 0 := ⟨_, fun x => Iff.rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, ∀ x, x ∈ B ↔ p x = 1 := ⟨_, fun x => Iff.rfl⟩
  refine ⟨fun _ => trivial, fun _ => ⟨A, B, ?_, ?_, ?_⟩⟩
  · ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true, hA, hB]
    have := hp1 x; omega
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, hA, hB]
    intros; omega
  · intro n
    have hG : ∀ a b, (n < a ∨ n < b) → (if a ≠ b ∧ a + b = n then 1 else 0 : ℕ) = 0 := by
      intro a b h
      rw [if_neg]
      rintro ⟨_, h2⟩
      omega
    have hN : ∀ S : Set ℕ, r S n = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if a ∈ S then (if b ∈ S then (if a ≠ b ∧ a + b = n then 1 else 0) else 0) else 0) := by
      intro S
      rw [hr S n]
      refine (tsum_congr fun x => tsum_congr fun y => ?_).trans
        (L1 n S (fun x y => if x ≠ y ∧ x + y = n then 1 else 0) hG)
      simp only [ne_eq, Subtype.ext_iff]
    have hL : ∀ S : Set ℕ, (r S n : ℤ) = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if a ∈ S then (if b ∈ S then (if a ≠ b ∧ a + b = n then (1:ℤ) else 0) else 0) else 0) := by
      intro S
      rw [hN S]
      push_cast
      rfl
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ → ℤ, ∀ a b, g a b = if a ≠ b ∧ a + b = n then 1 else 0 :=
      ⟨_, fun _ _ => rfl⟩
    have gsymm : ∀ a b, g a b = g b a := by
      intro a b
      rw [hg a b, hg b a]
      have : (b ≠ a ∧ b + a = n) ↔ (a ≠ b ∧ a + b = n) := by
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨fun h => h1 h.symm, by omega⟩
      simp only [this]
    have H : ∀ a b : ℕ, (2:ℤ) * (if a ∈ A then (if b ∈ A then g a b else 0) else 0)
        - 2 * (if a ∈ B then (if b ∈ B then g a b else 0) else 0) = g a b * (e a + e b) := by
      intro a b
      rw [he a, he b, hg a b]
      have ha := hp1 a
      have hb := hp1 b
      rcases (by omega : p a = 0 ∨ p a = 1) with h1 | h1 <;>
        rcases (by omega : p b = 0 ∨ p b = 1) with h2 | h2 <;>
        by_cases hg' : a ≠ b ∧ a + b = n <;>
        simp [hA, hB, h1, h2, hg']
    apply Nat.cast_injective (R := ℤ)
    rw [hL A, hL B]
    simp only [← hg]
    have S1 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        ((2:ℤ) * (if a ∈ A then (if b ∈ A then g a b else 0) else 0)
        - 2 * (if a ∈ B then (if b ∈ B then g a b else 0) else 0))
        = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * (e a + e b) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => H a b))
    have S1' : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        ((2:ℤ) * (if a ∈ A then (if b ∈ A then g a b else 0) else 0)
        - 2 * (if a ∈ B then (if b ∈ B then g a b else 0) else 0))
        = 2 * (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if a ∈ A then (if b ∈ A then g a b else 0) else 0))
          - 2 * (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
            (if a ∈ B then (if b ∈ B then g a b else 0) else 0)) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib]
    have S2 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e b
        = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e a := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by rw [gsymm]))
    have S3 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * (e a + e b)
        = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e a
          + ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e b := by
      simp only [mul_add, Finset.sum_add_distrib]
    have S4 : ∀ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e a
        = (if a ≠ n - a then (1:ℤ) else 0) * e a := by
      intro a ha
      rw [← Finset.sum_mul]
      congr 1
      simp only [hg]
      exact hinner n a (by simp at ha; omega)
    have S5 : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), g a b * e a = 0 := by
      rw [Finset.sum_congr rfl S4]
      exact hFinal n
    linarith [S1, S1', S2, S3, S5]
