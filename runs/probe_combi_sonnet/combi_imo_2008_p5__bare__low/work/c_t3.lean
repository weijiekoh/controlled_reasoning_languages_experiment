  have Rl : ∀ (n k : ℕ+) (f : Fin k → Fin (2*n)) (g : Fin k → Fin n) (b : Fin k → Bool)
      (hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((g j : Fin n) : ℕ) + if b j = true then (n:ℕ) else 0) (i : Fin n),
      (∑ j, if f j = (⟨i.val, by have := i.isLt; omega⟩ : Fin (2*n)) then 1 else 0) = (∑ j, if g j = i ∧ b j = false then 1 else 0) ∧
      (∑ j, if f j = (⟨i.val + n, by have := i.isLt; omega⟩ : Fin (2*n)) then 1 else 0) = (∑ j, if g j = i ∧ b j = true then 1 else 0) ∧
      (∑ j, if g j = i then 1 else 0) = (∑ j, if g j = i ∧ b j = false then 1 else 0) + (∑ j, if g j = i ∧ b j = true then 1 else 0) := by
    intro n k f g b hR i
    have hi := i.isLt
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.sum_congr rfl
      intro j _
      have h := hR j
      have e : (f j = (⟨i.val, by omega⟩ : Fin (2*n))) ↔ (g j = i ∧ b j = false) := by
        rw [Fin.ext_iff, Fin.ext_iff]
        cases hb : b j <;> simp [hb] at h ⊢ <;> omega
      exact if_congr e rfl rfl
    · apply Finset.sum_congr rfl
      intro j _
      have h := hR j
      have e : (f j = (⟨i.val + n, by omega⟩ : Fin (2*n))) ↔ (g j = i ∧ b j = true) := by
        rw [Fin.ext_iff, Fin.ext_iff]
        cases hb : b j <;> simp [hb] at h ⊢ <;> omega
      exact if_congr e rfl rfl
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases hb : b j <;> by_cases hg : g j = i <;> simp [hb, hg]
