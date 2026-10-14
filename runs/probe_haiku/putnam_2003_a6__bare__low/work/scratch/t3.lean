import Mathlib
open MvPolynomial Set

open Classical in
theorem X
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: ∀ S : Set ℕ, ∀ n : ℕ, r S n = ∑ a ∈ Finset.range (n+1), (if (a ≠ n - a ∧ a ∈ S ∧ n - a ∈ S) then 1 else 0 : ℕ) := by
  classical
  intro S n
  rw [hr]
  have h1 : ∀ x : S, ∑' s2 : S, (if (x ≠ s2 ∧ (x:ℕ) + (s2:ℕ) = n) then 1 else 0 : ℕ)
      = ∑' s2 : ℕ, S.indicator (fun y => (if (x.1 ≠ y ∧ x.1 + y = n) then 1 else 0 : ℕ)) s2 := by
    intro x
    rw [← _root_.tsum_subtype S (fun y : ℕ => (if (x.1 ≠ y ∧ x.1 + y = n) then 1 else 0 : ℕ))]
    apply tsum_congr
    intro s2
    simp [Subtype.ext_iff]
  have h2 : ∀ x : ℕ, ∑' s2 : ℕ, S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2
      = ∑ s2 ∈ Finset.range (n+1), S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2 := by
    intro x
    apply tsum_eq_sum
    intro b hb
    simp only [Finset.mem_range, not_lt] at hb
    simp only [Set.indicator]
    split_ifs with h3 h4 <;> first | rfl | (exfalso; omega) | skip

  simp only [h1]
  rw [_root_.tsum_subtype S (fun x : ℕ => ∑' s2 : ℕ, S.indicator (fun y => (if (x ≠ y ∧ x + y = n) then 1 else 0 : ℕ)) s2)]
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_range] at ha
    simp only [h2]
    by_cases haS : a ∈ S
    · rw [Set.indicator_of_mem haS]
      rw [Finset.sum_eq_single (n - a)]
      · by_cases hbS : n - a ∈ S
        · by_cases hne : a ≠ n - a
          · simp [Set.indicator, hne, haS, hbS]; omega
          · simp [Set.indicator, hne, haS, hbS]
        · simp [Set.indicator, hbS, haS]
      · intro b hb hbne
        simp only [Finset.mem_range] at hb
        simp only [Set.indicator]
        split_ifs with h3 h4 h5 <;> first | rfl | (exfalso; omega) | (exfalso; exact hbne (by omega))
      · intro h; exfalso; apply h; simp only [Finset.mem_range]; omega
    · simp [Set.indicator, haS]
  · intro b hb
    simp only [Finset.mem_range, not_lt] at hb
    simp only [Set.indicator]
    sorry
