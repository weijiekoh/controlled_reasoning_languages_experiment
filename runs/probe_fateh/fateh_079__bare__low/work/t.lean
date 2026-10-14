import Mathlib
theorem X {R : Type} [CommRing R]
    (h : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M],
      ∀ (N : Submodule R M), Module.Free R N) :
    IsPrincipalIdealRing R := by
  refine ⟨fun I => ?_⟩
  by_cases hs : Subsingleton R
  · exact ⟨⟨0, by ext x; simp [Subsingleton.elim x 0]⟩⟩
  rw [not_subsingleton_iff_nontrivial] at hs
  have := h R I
  let b := Module.Free.chooseBasis R I
  have hsub : ∀ i j : Module.Free.ChooseBasisIndex R I, i = j := by
    intro i j
    by_contra hij
    have hli := b.linearIndependent
    rw [linearIndependent_iff'] at hli
    have := hli {i, j} (fun k => if k = i then ((b j : I) : R) else if k = j then -((b i : I) : R) else 0) ?_ i (by simp)
    · simp at this
      exact b.ne_zero j (Subtype.ext (by simpa using this))
    · rw [Finset.sum_pair hij]
      simp [Ne.symm hij]
      apply Subtype.ext
      simp [mul_comm]
  by_cases hι : Nonempty (Module.Free.ChooseBasisIndex R I)
  · obtain ⟨i⟩ := hι
    refine ⟨⟨(b i : R), ?_⟩⟩
    ext x
    simp only [Submodule.mem_span_singleton, smul_eq_mul]
    constructor
    · intro hx
      have e : b.repr ⟨x, hx⟩ = Finsupp.single i (b.repr ⟨x, hx⟩ i) := by
        ext j
        rw [hsub j i]; simp
      have := b.repr.symm_apply_apply ⟨x, hx⟩
      rw [e] at this
      refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
      have := congrArg Subtype.val this
      simpa [Module.Basis.repr_symm_apply] using this
    · rintro ⟨c, rfl⟩
      exact I.smul_mem c (b i).2
  · rw [not_nonempty_iff] at hι
    refine ⟨⟨0, ?_⟩⟩
    ext x
    simp only [Submodule.mem_span_singleton, smul_eq_mul]
    constructor
    · intro hx
      have e : b.repr ⟨x, hx⟩ = 0 := by ext j; exact hι.elim j
      have : (⟨x, hx⟩ : I) = 0 := by simpa using e
      exact ⟨0, by simpa using congrArg Subtype.val this |>.symm⟩
    · rintro ⟨c, rfl⟩
      simp
