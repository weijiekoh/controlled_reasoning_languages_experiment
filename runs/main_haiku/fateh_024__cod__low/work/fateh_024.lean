import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  have hn : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  rw [eq_top_iff]
  rintro x -
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have key : H.index • (QuotientAddGroup.mk (q / (H.index : ℚ)) : ℚ ⧸ (Int.castAddHom ℚ).range) ∈ H :=
    AddSubgroup.nsmul_index_mem H _
  have heq : H.index • (QuotientAddGroup.mk (q / (H.index : ℚ)) : ℚ ⧸ (Int.castAddHom ℚ).range)
      = QuotientAddGroup.mk q := by
    rw [← QuotientAddGroup.mk_nsmul]
    congr 1
    have : (H.index : ℚ) ≠ 0 := by exact_mod_cast hn
    rw [nsmul_eq_mul]
    field_simp
  rw [heq] at key
  exact key
