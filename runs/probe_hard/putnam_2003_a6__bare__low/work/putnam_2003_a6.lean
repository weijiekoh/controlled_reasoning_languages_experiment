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
  have key : ∀ (S : Set ℕ) (n : ℕ), ∑' s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0 : ℕ) = ∑ a ∈ Finset.range (n+1), if (a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a) then 1 else 0 := by
    intro S n
    have h2 : ∀ s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0 : ℕ) = if (s1:ℕ) ≤ n ∧ n - s1 ∈ S ∧ (s1:ℕ) ≠ n - s1 then 1 else 0 := by
      intro s1
      by_cases h : (s1:ℕ) ≤ n ∧ n - s1 ∈ S ∧ (s1:ℕ) ≠ n - s1
      · rw [if_pos h, tsum_eq_single ⟨n - s1, h.2.1⟩]
        · rw [if_pos]; constructor
          · intro e; apply h.2.2; exact congrArg Subtype.val e
          · show (s1:ℕ) + (n - s1) = n; omega
        · intro b hb; rw [if_neg]; rintro ⟨_, e⟩
          apply hb; apply Subtype.ext; have := b.2; simp at e ⊢; omega
      · rw [if_neg h]
        have : ∀ b : S, (if (s1 ≠ b ∧ s1 + b = n) then 1 else 0 : ℕ) = 0 := by
          intro b; rw [if_neg]; rintro ⟨h1, e⟩
          apply h; refine ⟨by omega, ?_, ?_⟩
          · have : n - (s1:ℕ) = b := by omega
            rw [this]; exact b.2
          · intro e2; apply h1; apply Subtype.ext; omega
        simp [this]
    simp_rw [h2]
    rw [tsum_subtype S (fun a => if a ≤ n ∧ n - a ∈ S ∧ a ≠ n - a then (1:ℕ) else 0)]
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    · apply Finset.sum_congr rfl
      intro a ha
      simp only [Set.indicator]
      by_cases h : a ∈ S <;> simp [h] at *
      all_goals simp [ha]
    · intro a ha
      simp at ha
      simp [Set.indicator]; intro _ h; omega
  let g : ℕ → ℤ := fun n => if Even (Nat.digits 2 n).sum then 1 else -1
  have g0 : ∀ k, g (2*k) = g k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp only [g]
      rw [Nat.digits_def' (by norm_num) (by omega)]
      simp
  have g1 : ∀ k, g (2*k+1) = - g (2*k) := by
    intro k
    simp only [g]
    rw [Nat.digits_def' (by norm_num) (by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.digits_def' (by norm_num) (by omega) (n := 2*k)]
      have e1 : (2*k+1)%2 = 1 := by omega
      have e2 : (2*k+1)/2 = k := by omega
      have e3 : (2*k)%2 = 0 := by omega
      have e4 : (2*k)/2 = k := by omega
      rw [e1, e2, e3, e4]
      by_cases h : Even (Nat.digits 2 k).sum <;> simp [h, Nat.even_add_one, add_comm 1, parity_simps]
  have S2 : ∀ m, ∑ a ∈ Finset.range (2*m), g a = 0 := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, g1]; ring
  have T : ∀ n, ∑ a ∈ Finset.range (n+1), g a = if Even n then g (n/2) else 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [Finset.sum_range_succ, S2, if_pos (by simp)]; simp [g0]
    · rw [show 2*m+1+1 = 2*m+1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, S2, g1]
      rw [if_neg (by simp [Nat.even_add_one])]; ring
  have P : ∀ n, ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then g a + g (n-a) else 0) = 0 := by
    intro n
    have R : ∑ a ∈ Finset.range (n+1), g (n-a) = ∑ a ∈ Finset.range (n+1), g a := by
      rw [← Finset.sum_range_reflect]; apply Finset.sum_congr rfl; intro a ha; simp at ha; congr 1; omega
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then g a + g (2*m-a) else 0) = (g a + g (2*m-a)) - if m = a then 2 * g m else 0 := by
        intro a ha
        by_cases h : m = a
        · subst h; have e : 2*m-m = m := by omega
          simp [e]; ring
        · rw [if_neg h, if_pos (by omega)]; simp
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_add_distrib, R, T, Finset.sum_ite_eq]
      simp [g0]; rw [if_pos (by omega)]; ring
    · have : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then g a + g (2*m+1-a) else 0) = (g a + g (2*m+1-a)) := by
        intro a ha; rw [if_pos (by omega)]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, R, T, if_neg (by simp [Nat.even_add_one])]; ring
  constructor
  · intro _; trivial
  · intro _
    refine ⟨{n | Even (Nat.digits 2 n).sum}, {n | ¬ Even (Nat.digits 2 n).sum}, ?_, ?_, ?_⟩
    · ext n; by_cases h : Even (Nat.digits 2 n).sum <;> simp [h] <;> exact Nat.not_even_iff_odd.mp h
    · ext n; simp
    · intro n
      rw [hr, hr, key, key]
      have h := P n
      have h2 : ∀ a ∈ Finset.range (n+1), (2:ℤ) * (((if (a ∈ {n | Even (Nat.digits 2 n).sum} ∧ n - a ∈ {n | Even (Nat.digits 2 n).sum} ∧ a ≠ n - a) then 1 else 0 : ℕ) : ℤ) - ((if (a ∈ {n | ¬ Even (Nat.digits 2 n).sum} ∧ n - a ∈ {n | ¬ Even (Nat.digits 2 n).sum} ∧ a ≠ n - a) then 1 else 0 : ℕ) : ℤ)) = if a ≠ n - a then g a + g (n-a) else 0 := by
        intro a _
        simp only [Set.mem_setOf_eq]
        generalize n - a = b
        by_cases p : Even (Nat.digits 2 a).sum <;> by_cases q : Even (Nat.digits 2 b).sum <;> by_cases e : a = b <;> simp [g, p, q, e]
      have h3 := Finset.sum_congr rfl h2
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, h] at h3
      have : ((∑ a ∈ Finset.range (n+1), (if (a ∈ {n | Even (Nat.digits 2 n).sum} ∧ n - a ∈ {n | Even (Nat.digits 2 n).sum} ∧ a ≠ n - a) then 1 else 0 : ℕ) : ℕ) : ℤ) = ((∑ a ∈ Finset.range (n+1), (if (a ∈ {n | ¬ Even (Nat.digits 2 n).sum} ∧ n - a ∈ {n | ¬ Even (Nat.digits 2 n).sum} ∧ a ≠ n - a) then 1 else 0 : ℕ) : ℕ) : ℤ) := by
        push_cast at h3 ⊢; linarith
      first | exact Int.ofNat.inj this | (simp only [Nat.cast_inj] at this; convert this) | (convert Int.ofNat.inj this)
