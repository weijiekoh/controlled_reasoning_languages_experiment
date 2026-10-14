import Mathlib
open Polynomial IntermediateField

theorem twogen (K L : Type) [Field K] [Field L] [Algebra K L] [Infinite K]
    (α β : L) (hα : IsIntegral K α) (hβ : IsSeparable K β) :
    ∃ γ : L, K⟮α, β⟯ = K⟮γ⟯ := by
  sorry

theorem X (p : ℕ) [Fact (Nat.Prime p)]
    (K L : Type) [Field K] [Field L] [CharP L p] [Algebra K L] [FiniteDimensional K L]
    (h : Module.rank (IntermediateField.adjoin K ((frobenius L p).range : Set L)) L ≤ p) :
    ∃ (x : L), IntermediateField.adjoin K {x} = ⊤ := by
  classical
  haveI : ExpChar L p := ExpChar.prime (Fact.out)
  by_cases hK : Finite K
  · haveI : Finite L := Module.finite_of_finite K
    exact Field.exists_primitive_element_of_finite_top K L
  haveI : Infinite K := not_finite_iff_infinite.1 hK
  set F := IntermediateField.adjoin K ((frobenius L p).range : Set L) with hFdef
  have hFp : ∀ y : L, y ^ p ∈ F := fun y =>
    subset_adjoin K _ ⟨y, rfl⟩
  have hfr : Module.finrank F L ≤ p := by
    have h2 : (Module.finrank F L : Cardinal) ≤ p := by rw [Module.finrank_eq_rank]; exact h
    exact_mod_cast h2
  haveI : CharP F p := (RingHom.charP_iff (F.val : F →+* L) (F.val : F →+* L).injective p).2 inferInstance
  haveI : ExpChar F p := ExpChar.prime (Fact.out)
  haveI : IsPurelyInseparable F L := by
    rw [isPurelyInseparable_iff_pow_mem F p]
    intro x
    exact ⟨1, by simpa using hFp x⟩
  -- Step B
  have hB : ∃ a : L, ∀ E : IntermediateField K L, F ≤ E → a ∈ E → E = ⊤ := by
    by_cases hFt : F = ⊤
    · exact ⟨0, fun E hE _ => top_le_iff.1 (hFt ▸ hE)⟩
    obtain ⟨a, haF⟩ : ∃ a : L, a ∉ F := by
      by_contra hcon
      push_neg at hcon
      exact hFt (top_le_iff.1 fun x _ => hcon x)
    have hadj : F⟮a⟯ = ⊤ := by
      obtain ⟨m, y, hm⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
      have hdeg : (minpoly F a).natDegree = p ^ m := by
        rw [hm]; exact natDegree_X_pow_sub_C
      have hm1 : m ≠ 0 := by
        rintro rfl
        have : (minpoly F a).natDegree = 1 := by simpa using hdeg
        obtain ⟨e, he⟩ := minpoly.natDegree_eq_one_iff.1 this
        exact haF (he ▸ e.2)
      have hp : p ≤ p ^ m := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.one_le_iff_ne_zero.2 hm1)
      have hfin : Module.finrank F F⟮a⟯ = p ^ m := by
        rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite F a), hdeg]
      apply IntermediateField.eq_of_le_of_finrank_le le_top
      rw [hfin, IntermediateField.finrank_top']
      omega
    refine ⟨a, fun E hFE haE => ?_⟩
    have : F⟮a⟯ ≤ IntermediateField.extendScalars hFE := by
      rw [adjoin_simple_le_iff]; exact haE
    rw [hadj] at this
    apply top_le_iff.1
    intro x _
    exact (mem_extendScalars (hFE)).1 (this (mem_top))
  obtain ⟨a, ha⟩ := hB
  sorry
