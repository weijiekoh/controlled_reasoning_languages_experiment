import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hn : H.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have hnq : (H.index : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmem := AddSubgroup.nsmul_index_mem H (QuotientAddGroup.mk (q / (H.index : ℚ)))
  have heq : H.index • (QuotientAddGroup.mk (q / (H.index : ℚ)) : ℚ ⧸ (Int.castAddHom ℚ).range)
      = QuotientAddGroup.mk q := by
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
    congr 1
    field_simp
  rw [heq] at hmem
  exact hmem
