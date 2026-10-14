import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hn : H.index ≠ 0 := h_fin.index_ne_zero
  have := AddSubgroup.nsmul_index_mem H (QuotientAddGroup.mk (s := (Int.castAddHom ℚ).range) (q / H.index))
  convert this using 1
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  field_simp
