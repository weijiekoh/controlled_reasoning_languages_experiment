lemma memEq (n k : ℕ+) (f : Fin k → Fin (2*n)) (g : Fin k → Fin n) (b : Fin k → Bool)
    (hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((g j : Fin n) : ℕ) + if b j = true then (n:ℕ) else 0) :
    (∀ x : Fin (2*n), Odd (∑ j, if f j = x then 1 else 0) ↔ x.val < n) ↔
    ((∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0)) ∧ ∀ i : Fin n, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0)) := by
  have hl1 : ∀ i : Fin n, i.val < 2*n := fun i => by have := i.isLt; omega
  have hl2 : ∀ i : Fin n, i.val + n < 2*n := fun i => by have := i.isLt; omega
  constructor
  · intro h
    constructor
    · intro i
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      have h1 := (h ⟨i.val, by have := i.isLt; omega⟩).2 i.isLt
      have h2 := h ⟨i.val + n, by have := i.isLt; omega⟩
      simp only [ha] at h1
      simp only [hb] at h2
      have h3 : ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0) := by
        intro ho; have := h2.1 ho; omega
      rw [hc]
      simp only [Nat.odd_iff] at h1 h3 ⊢
      omega
    · intro i
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      have h2 := h ⟨i.val + n, by have := i.isLt; omega⟩
      simp only [hb] at h2
      intro ho; have := h2.1 ho; omega
  · rintro ⟨h1, h2⟩ x
    by_cases hx : x.val < n
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, x = ⟨i.val, hl1 i⟩ := ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
      subst hi
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      simp only [ha]
      have a1 := h1 i
      have a2 := h2 i
      rw [hc] at a1
      simp only [Nat.odd_iff] at a1 a2 ⊢
      simp only [i.isLt, iff_true]
      omega
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, x = ⟨i.val + n, hl2 i⟩ := ⟨⟨x.val - n, by have := x.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      subst hi
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      simp only [hb]
      simp only [Fin.val_mk] at hx ⊢
      simp only [hx, iff_false]
      exact h2 i
