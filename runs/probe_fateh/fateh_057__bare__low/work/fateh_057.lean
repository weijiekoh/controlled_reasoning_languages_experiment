import Mathlib

/--
If $F$ is a field that is not perfect, show that $F$ has a nontrivial purely inseparable
extension.
-/
theorem exists_isPurelyInseparable_and_bot_lt {F : Type} [Field F] (h : ¬ PerfectField F) :
    ∃ E : IntermediateField F (AlgebraicClosure F), IsPurelyInseparable F E ∧ ⊥ < E := by
  obtain ⟨p, hp⟩ := ExpChar.exists F
  have hpp : p.Prime := by
    cases hp with
    | zero => exact absurd (PerfectField.ofCharZero) h
    | prime h => exact h
  have : ¬ Function.Surjective (frobenius F p) := fun hs =>
    h (haveI := PerfectRing.ofSurjective F p hs; PerfectRing.toPerfectField F p)
  simp only [Function.Surjective, not_forall, not_exists] at this
  obtain ⟨a, ha⟩ := this
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) a) hpp.pos
  refine ⟨perfectClosure F (AlgebraicClosure F), inferInstance, ?_⟩
  rw [bot_lt_iff_ne_bot, Ne]
  intro hb
  have hm : α ∈ perfectClosure F (AlgebraicClosure F) := by
    rw [mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, by simpa using ⟨a, hα.symm⟩⟩
  rw [hb, IntermediateField.mem_bot] at hm
  obtain ⟨x, hx⟩ := hm
  apply ha x
  apply (algebraMap F (AlgebraicClosure F)).injective
  simp only [frobenius_def, map_pow]
  rw [hx]; exact hα
