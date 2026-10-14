import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  classical
  have hn : H.index ≠ 0 := by
    exact AddSubgroup.index_ne_zero_of_finite
  rw [eq_top_iff]
  intro x _
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have key : (H.index) • (QuotientAddGroup.mk (q / (H.index : ℚ)) : ℚ ⧸ (Int.castAddHom ℚ).range) = QuotientAddGroup.mk q := by
    have h1 := map_nsmul (QuotientAddGroup.mk' ((Int.castAddHom ℚ).range)) H.index (q / (H.index : ℚ))
    simp only [QuotientAddGroup.mk'_apply] at h1
    rw [← h1]
    congr 1
    rw [nsmul_eq_mul]
    have : (H.index : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp
  rw [← key]
  exact AddSubgroup.nsmul_index_mem H _
