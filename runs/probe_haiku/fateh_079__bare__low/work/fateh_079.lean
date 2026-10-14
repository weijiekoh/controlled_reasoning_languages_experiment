import Mathlib

/--
Let \( R \) be a commutative ring. If all submodules of finitely generated free modules over
\( R \) are free over \( R \), then \( R \) is a PID.
-/
theorem isPrincipalIdealRing_of_forall_free {R : Type} [CommRing R]
    (h : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M],
      ∀ (N : Submodule R M), Module.Free R N) :
    IsPrincipalIdealRing R := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨fun I => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨fun I => ?_⟩
  have : Module.Free R I := h R I
  set b := Module.Free.chooseBasis R I with hb
  have hsub : ∀ i j : Module.Free.ChooseBasisIndex R I, i = j := by
    intro i j
    by_contra hij
    have hli : LinearIndependent R ![b i, b j] := by
      have hinj : Function.Injective ![i, j] := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
      have := b.linearIndependent.comp ![i, j] hinj
      convert this using 1
      ext k; fin_cases k <;> rfl
    rw [LinearIndependent.pair_iff] at hli
    have hrelI : ((b j : I) : R) • b i + (-((b i : I) : R)) • b j = (0 : I) := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, Submodule.coe_zero]
      ring
    obtain ⟨_, ht⟩ := hli _ _ hrelI
    have : b i = 0 := by
      apply Subtype.ext
      simpa using ht
    exact b.ne_zero i this
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex R I) with hE | hN
  · refine ⟨⟨0, ?_⟩⟩
    have hbot : I = ⊥ := by
      ext y
      constructor
      · intro hy
        have hm : (⟨y, hy⟩ : I) ∈ Submodule.span R (Set.range b) := by
          rw [b.span_eq]; trivial
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hm
        have := congrArg Subtype.val hm
        simpa using this
      · intro hy
        rw [Submodule.mem_bot] at hy
        simp [hy]
    rw [hbot]; simp
  · obtain ⟨i⟩ := hN
    have : Unique (Module.Free.ChooseBasisIndex R I) :=
      ⟨⟨i⟩, fun j => hsub _ _⟩
    have key : ∀ y : I, ∃ c : R, c • b default = y := by
      intro y
      have hm : y ∈ Submodule.span R (Set.range b) := by
        rw [b.span_eq]; trivial
      rw [Set.range_unique, Submodule.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      exact ⟨c, hc⟩
    refine ⟨(b default : R), ?_⟩
    ext y
    rw [Submodule.mem_span_singleton]
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := key ⟨y, hy⟩
      refine ⟨c, ?_⟩
      have := congrArg Subtype.val hc
      simpa using this
    · rintro ⟨c, rfl⟩
      exact I.mul_mem_left c (b default).2
