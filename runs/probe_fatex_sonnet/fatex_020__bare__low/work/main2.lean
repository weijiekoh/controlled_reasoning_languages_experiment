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
  -- Step C
  set S := separableClosure K L with hS
  haveI : CharP S p := (RingHom.charP_iff (S.val : S →+* L) (S.val : S →+* L).injective p).2 inferInstance
  haveI : ExpChar S p := ExpChar.prime (Fact.out)
  haveI : IsPurelyInseparable S L := separableClosure.isPurelyInseparable K L
  have hC : ∃ n : ℕ, ∀ x : L, x ^ p ^ n ∈ S := by
    refine ⟨Module.finrank S L, fun x => ?_⟩
    obtain ⟨m, y, hm⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C S p x
    have hdeg : (minpoly S x).natDegree = p ^ m := by
      rw [hm]; exact natDegree_X_pow_sub_C
    have hle : p ^ m ≤ Module.finrank S L := hdeg ▸ minpoly.natDegree_le x
    have hmlt : m < p ^ m := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have hmd : m ≤ Module.finrank S L := by omega
    have hx : x ^ p ^ m = algebraMap S L y := by
      have := minpoly.aeval S x
      rw [hm] at this
      simp at this
      exact sub_eq_zero.1 this
    have : x ^ p ^ Module.finrank S L = (x ^ p ^ m) ^ p ^ (Module.finrank S L - m) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hmd]
    rw [this, hx]
    exact pow_mem (y.2) _
  obtain ⟨n, hn⟩ := hC
  -- Step D
  let M : IntermediateField K L := K⟮a⟯
  let E : ℕ → IntermediateField K L := fun j =>
    M ⊔ IntermediateField.adjoin K (Set.range (fun x : L => x ^ p ^ j))
  have hE : ∀ j, E j = ⊤ := by
    intro j
    induction j with
    | zero =>
      apply top_le_iff.1
      intro x _
      apply (le_sup_right : _ ≤ E 0)
      exact subset_adjoin K _ ⟨x, by simp⟩
    | succ j ih =>
      let Q := E (j + 1)
      let PQ : IntermediateField K L :=
        { carrier := {x | x ^ p ∈ Q}
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, mul_pow]; exact mul_mem ha hb
          one_mem' := by simp
          add_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, add_pow_char]; exact add_mem ha hb
          zero_mem' := by
            simp only [Set.mem_setOf_eq]
            rw [zero_pow (Fact.out : p.Prime).ne_zero]; exact zero_mem _
          algebraMap_mem' := fun k => by
            simp only [Set.mem_setOf_eq, ← map_pow]; exact IntermediateField.algebraMap_mem Q _
          inv_mem' := fun x hx => by
            simp only [Set.mem_setOf_eq, inv_pow] at hx ⊢; exact inv_mem hx }
      have hMQ : M ≤ Q := le_sup_left
      have hle : E j ≤ PQ := by
        apply sup_le
        · intro x hx
          exact hMQ (pow_mem hx p)
        · rw [adjoin_le_iff]
          rintro x ⟨y, rfl⟩
          show (y ^ p ^ j) ^ p ∈ Q
          rw [← pow_mul, ← pow_succ]
          exact (le_sup_right : IntermediateField.adjoin K (Set.range (fun x : L => x ^ p ^ (j+1))) ≤ Q) (subset_adjoin K _ ⟨y, rfl⟩)
      have hall : ∀ x : L, x ^ p ∈ Q := fun x => hle (ih ▸ mem_top)
      apply ha Q
      · rw [hFdef, adjoin_le_iff]
        rintro x ⟨y, rfl⟩
        exact hall y
      · exact hMQ (mem_adjoin_simple_self K a)
  sorry
