import Mathlib
open Classical in
example (S : Set ℕ) (n : ℕ) : ∑' s1 : S, ∑' s2 : S, (if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0 : ℕ) = ∑ a ∈ Finset.range (n+1), if (a ∈ S ∧ n - a ∈ S ∧ a ≠ n - a) then 1 else 0 := by
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
