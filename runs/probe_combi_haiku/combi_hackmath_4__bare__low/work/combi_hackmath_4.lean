import Mathlib

noncomputable abbrev hackmath_4_solution : ℕ := 13

/--
How many people must be in a group for at least two of them to be born in the same month?
-/
theorem hackmath_4 : IsLeast {n | ∀ f : Fin n → Fin 12, ∃ a b, a ≠ b ∧ f a = f b} hackmath_4_solution := by
  constructor
  · intro f
    exact Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  · intro n hn
    by_contra h
    have h' : n ≤ 12 := by
      unfold hackmath_4_solution at h
      omega
    obtain ⟨a, b, hab, hf⟩ := hn (fun i => ⟨i.val, by have := i.isLt; omega⟩)
    apply hab
    ext
    have := congrArg Fin.val hf
    simpa using this
