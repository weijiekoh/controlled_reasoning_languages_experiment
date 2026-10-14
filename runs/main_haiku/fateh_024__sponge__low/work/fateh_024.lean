import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  have hn : H.index ≠ 0 := by
    haveI := h_fin
    exact AddSubgroup.index_ne_zero_of_finite
  induction g using QuotientAddGroup.induction_on with
  | H q =>
    have key : ((H.index : ℕ) • (QuotientAddGroup.mk (((q : ℚ) / (H.index : ℚ))) : ℚ ⧸ (Int.castAddHom ℚ).range)) = QuotientAddGroup.mk q := by
      rw [← QuotientAddGroup.mk_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      have : (H.index : ℚ) ≠ 0 := by exact_mod_cast hn
      push_cast
      field_simp
    rw [← key]
    exact AddSubgroup.nsmul_index_mem H _
