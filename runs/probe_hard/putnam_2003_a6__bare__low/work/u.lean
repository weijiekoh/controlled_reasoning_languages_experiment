import Mathlib
open Classical in
example : True := by
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
  trivial
