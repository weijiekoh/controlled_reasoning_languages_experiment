import Mathlib

noncomputable abbrev hackmath_4_solution : ℕ := 13

/--
How many people must be in a group for at least two of them to be born in the same month?
-/
theorem hackmath_4 : IsLeast {n | ∀ f : Fin n → Fin 12, ∃ a b, a ≠ b ∧ f a = f b} hackmath_4_solution := by
  constructor
  · intro f
    by_contra h
    push_neg at h
    have := Fintype.card_le_of_injective f (fun a b hab => by
      by_contra hne; exact h a b hne hab)
    unfold hackmath_4_solution at this; simp at this
  · intro n hn
    by_contra hlt
    push_neg at hlt
    obtain ⟨a, b, hne, h⟩ := hn (fun i => ⟨i.val, by have := i.2; unfold hackmath_4_solution at hlt; omega⟩)
    apply hne
    ext
    simpa using h
