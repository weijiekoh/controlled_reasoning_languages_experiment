import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True

def tmS (n : ℕ) : ℤ := if Even (Nat.digits 2 n).sum then 1 else -1

lemma tmS_cases (n : ℕ) : tmS n = 1 ∨ tmS n = -1 := by
  unfold tmS; split_ifs <;> simp

lemma tmS_double (m : ℕ) : tmS (2*m) = tmS m ∧ tmS (2*m+1) = - tmS m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : Nat.digits 2 1 = [1] := Nat.digits_of_lt 2 1 one_ne_zero one_lt_two
    simp [tmS]
  · constructor
    · have h1 : 0 < 2*m := by omega
      have h2 : 2*m % 2 = 0 := by omega
      have h3 : 2*m/2 = m := by omega
      unfold tmS
      rw [Nat.digits_def' (by norm_num) h1, h2, h3, List.sum_cons]
      simp
    · have h1 : 0 < 2*m+1 := by omega
      have h2 : (2*m+1) % 2 = 1 := by omega
      have h3 : (2*m+1)/2 = m := by omega
      unfold tmS
      rw [Nat.digits_def' (by norm_num) h1, h2, h3, List.sum_cons]
      by_cases h : Even (Nat.digits 2 m).sum <;> simp [Nat.even_add, h]

lemma tmS_sum_even (m : ℕ) : ∑ a ∈ Finset.range (2*m), tmS a = 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    obtain ⟨h1, h2⟩ := tmS_double k
    rw [h1, h2]; ring

lemma tmS_sum_odd (m : ℕ) : ∑ a ∈ Finset.range (2*m+1), tmS a = tmS m := by
  rw [Finset.sum_range_succ, tmS_sum_even, zero_add, (tmS_double m).1]

lemma tmS_Q (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (if j = n - j then tmS j else 0)
      = ∑ j ∈ Finset.range (n+1), tmS j := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : m = 2*m - m := by omega
    rw [Finset.sum_eq_single m, tmS_sum_odd, if_pos hm]
    · intro j hj hjm
      rw [Finset.mem_range] at hj
      have : j ≠ 2*m - j := by omega
      rw [if_neg this]
    · intro h
      exfalso; apply h; rw [Finset.mem_range]; omega
  · have h0 : ∑ j ∈ Finset.range (2*m+1+1), (if j = 2*m+1 - j then tmS j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (show j ≠ 2*m+1-j by omega)]
    rw [h0, show 2*m+1+1 = 2*(m+1) by ring, tmS_sum_even]

lemma tmS_zero_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (if j ≠ n - j then tmS j else 0) = 0 := by
  have h : ∀ j ∈ Finset.range (n+1),
      (if j ≠ n - j then tmS j else 0) = tmS j - (if j = n - j then tmS j else 0) := by
    intro j _
    by_cases h : j = n - j
    · rw [if_neg (fun hne => hne h), if_pos h, sub_self]
    · rw [if_pos h, if_neg h, sub_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, tmS_Q, sub_self]

lemma tmS_pair (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then tmS a + tmS (n - a) else 0) = 0 := by
  have hrefl : ∑ j ∈ Finset.range (n+1), (if n - j ≠ n - (n - j) then tmS (n - j) else 0)
      = ∑ j ∈ Finset.range (n+1), (if j ≠ n - j then tmS j else 0) := by
    have := Finset.sum_range_reflect (fun j => if j ≠ n - j then tmS j else 0) (n+1)
    simpa using this
  have hcongr : ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then tmS (n - a) else 0)
      = ∑ j ∈ Finset.range (n+1), (if n - j ≠ n - (n - j) then tmS (n - j) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show n - (n - j) = j by omega]
    by_cases h : j = n - j
    · rw [if_neg (fun hne => hne h), if_neg (fun e => e h.symm)]
    · have h' : n - j ≠ j := fun e => h e.symm
      rw [if_pos h, if_pos h']
  have hsplit : ∀ a ∈ Finset.range (n+1),
      (if a ≠ n - a then tmS a + tmS (n - a) else 0)
        = (if a ≠ n - a then tmS a else 0) + (if a ≠ n - a then tmS (n - a) else 0) := by
    intro a _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcongr, hrefl, tmS_zero_sum, add_zero]

lemma my_sum_collapse (g : ℕ → ℕ → ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), (if a + b = n then g a b else 0)
      = ∑ a ∈ Finset.range (n+1), g a (n - a) := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_range] at ha
  rw [Finset.sum_eq_single (n - a)]
  · rw [if_pos (show a + (n - a) = n by omega)]
  · intro b _ hb
    rw [if_neg (show ¬ (a + b = n) by omega)]
  · intro h
    exfalso; apply h; rw [Finset.mem_range]; omega

lemma inner_eq (S : Set ℕ) [DecidablePred (· ∈ S)] (a n : ℕ) :
    (∑' s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 : ℕ))
      = ∑ b ∈ Finset.range (n+1), (if (b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) := by
  refine (tsum_subtype S (fun b : ℕ => (if (a ≠ b ∧ a + b = n) then 1 else 0 : ℕ))).trans ?_
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Set.indicator_apply]
    by_cases hS : b ∈ S <;> simp [hS]
  · intro b hb
    rw [Finset.mem_range, not_lt] at hb
    simp only [Set.indicator_apply]
    split_ifs <;> omega

lemma r_eq (S : Set ℕ) [DecidablePred (· ∈ S)] (n : ℕ) :
    (∑' s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ))
      = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
          (if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℕ) := by
  let f : ℕ → ℕ := fun a => ∑' s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 : ℕ)
  have e1 : (∑' s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ))
      = ∑' s1 : S, f (s1:ℕ) := by
    apply tsum_congr; intro s1
    show _ = ∑' s2 : S, (if ((s1:ℕ) ≠ (s2:ℕ) ∧ (s1:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ)
    apply tsum_congr; intro s2
    simp only [ne_eq, Subtype.ext_iff]
  rw [e1, tsum_subtype S f, tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Set.indicator_apply]
    by_cases ha : a ∈ S
    · rw [if_pos ha]
      show (∑' s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 : ℕ)) = _
      rw [inner_eq S a n]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∈ S <;> simp [ha, hb]
    · rw [if_neg ha]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg (fun h => ha h.1)]
  · intro a ha
    rw [Finset.mem_range, not_lt] at ha
    rw [Set.indicator_apply]
    split_ifs with hS
    · show (∑' s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 : ℕ)) = 0
      have h0 : ∀ s2 : S, (if (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 : ℕ) = 0 := by
        intro s2
        rw [if_neg (show ¬ (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) by intro h; omega)]
      simp only [h0, tsum_zero]
    · rfl

lemma diff_zero (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA : ∀ a, a ∈ A ↔ tmS a = 1) (hB : ∀ a, a ∈ B ↔ tmS a = -1) (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      ((if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ)
        - (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ)) = 0 := by
  have h1 : ∀ a b : ℕ, 2 * ((if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ)
        - (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ))
      = (if a + b = n then (if a ≠ b then tmS a + tmS b else 0) else 0) := by
    intro a b
    by_cases hne : a = b
    · subst hne
      simp
    · rcases tmS_cases a with h1 | h1 <;> rcases tmS_cases b with h2 | h2 <;>
        by_cases hab : a + b = n <;> simp [hA, hB, h1, h2, hab, hne]
  have h3 : 2 * (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      ((if (a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ)
        - (if (a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ a + b = n) then 1 else 0 : ℤ)))
      = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if a + b = n then (if a ≠ b then tmS a + tmS b else 0) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact h1 a b
  have h4 : (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (if a + b = n then (if a ≠ b then tmS a + tmS b else 0) else 0))
      = ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then tmS a + tmS (n - a) else 0) :=
    my_sum_collapse (fun a b => if a ≠ b then tmS a + tmS b else 0) n
  rw [h4, tmS_pair] at h3
  linarith

theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution :=
by
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  refine ⟨{n | tmS n = 1}, {n | tmS n = -1}, ?_, ?_, ?_⟩
  · ext n
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ]
    exact iff_of_true (tmS_cases n) trivial
  · ext n
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rw [h1] at h2
    norm_num at h2
  · intro n
    rw [hr, hr, r_eq, r_eq]
    have key := diff_zero {n | tmS n = 1} {n | tmS n = -1} (fun a => Iff.rfl) (fun a => Iff.rfl) n
    simp only [Finset.sum_sub_distrib] at key
    apply Nat.cast_injective (R := ℤ)
    push_cast
    linarith
