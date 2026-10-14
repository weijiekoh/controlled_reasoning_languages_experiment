lemma Bc (n : ℕ+) (k : ℕ) (f : Fin k → Fin (2*n)) : lamps_final_state n (List.ofFn f) = final_goal n ↔ ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n := by
  rw [A, final_goal, List.ofFn_inj, funext_iff]
  simp

lemma Cc (n : ℕ+) (k : ℕ) (g : Fin k → Fin n) (i : Fin (2*n)) :
    (∑ j, if (Fin.castLE (by omega : (n:ℕ) ≤ 2 * n) (g j)) = i then 1 else 0) = if h : i.val < n then ∑ j, if g j = ⟨i, h⟩ then 1 else 0 else 0 := by
  by_cases h : i.val < n
  · rw [dif_pos h]
    apply Finset.sum_congr rfl
    intro j _
    exact if_congr (by simp [Fin.ext_iff]) rfl rfl
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have := (g j).isLt
    rw [if_neg]
    intro e
    rw [← e] at h
    simp at h
