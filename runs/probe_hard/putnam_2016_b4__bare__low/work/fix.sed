/^  subst hmats01$/d
s/^        intro i j; simp only \[Mf, vv\]; split_ifs <;> simp⟩/        rw [hm]; intro i j; simp only [Mf, vv]; split_ifs <;> simp⟩/
s/^        have := A.2; simp only \[Set.mem_setOf_eq\] at this/        have := (hm A.1).mp A.2/
s/^  let e : (Fin (2\*n)/  have hm : ∀ M, M ∈ mats01 ↔ ∀ i j : Fin (2 * n), M i j = 0 ∨ M i j = 1 := by\n    intro M; rw [hmats01]; rfl\n  let e : (Fin (2*n)/
