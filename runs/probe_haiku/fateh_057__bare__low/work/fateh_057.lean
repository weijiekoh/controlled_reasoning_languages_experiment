import Mathlib

/--
If $F$ is a field that is not perfect, show that $F$ has a nontrivial purely inseparable
extension.
-/
theorem exists_isPurelyInseparable_and_bot_lt {F : Type} [Field F] (h : ¬ PerfectField F) :
    ∃ E : IntermediateField F (AlgebraicClosure F), IsPurelyInseparable F E ∧ ⊥ < E := by
  obtain ⟨p, hp⟩ := ExpChar.exists F
  cases hp with
  | zero => exact absurd PerfectField.ofCharZero h
  | prime hpr =>
    rename_i hchar
    have hE : ExpChar F p := ExpChar.prime hpr
    have hp2 : 0 < p := hpr.pos
    have hx : ∃ x : F, ∀ y : F, y ^ p ≠ x := by
      by_contra hcon
      push Not at hcon
      apply h
      letI : PerfectRing F p :=
        ⟨⟨fun a b hab => (frobenius F p).injective hab, fun x => hcon x⟩⟩
      exact PerfectRing.toPerfectField F p
    obtain ⟨x, hx⟩ := hx
    have hdeg : (Polynomial.X ^ p - Polynomial.C (algebraMap F (AlgebraicClosure F) x)).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C hp2]
      exact_mod_cast hpr.ne_zero
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    have hyp : y ^ p = algebraMap F (AlgebraicClosure F) x := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at hy
      exact sub_eq_zero.mp hy
    refine ⟨IntermediateField.adjoin F {y}, ?_, ?_⟩
    · rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F _ p]
      exact ⟨1, by rw [pow_one, hyp]; exact ⟨x, rfl⟩⟩
    · refine lt_of_le_of_ne bot_le ?_
      intro heq
      have hmem : y ∈ IntermediateField.adjoin F {y} := IntermediateField.mem_adjoin_simple_self F y
      rw [← heq, IntermediateField.mem_bot] at hmem
      obtain ⟨z, hz⟩ := hmem
      apply hx z
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [map_pow, hz, hyp]
