import Mathlib

section gen
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma ch_sum_eq (z : H) : ∑ ψ : AddChar H ℂ, ψ z = if z = 0 then (Fintype.card H : ℂ) else 0 := by
  rw [AddChar.sum_apply_eq_ite]

lemma ch_inv (F : H → ℂ) (x : H) :
    ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, F y * ψ y = (Fintype.card H : ℂ) * F x := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ y, ∑ ψ : AddChar H ℂ, ψ (-x) * (F y * ψ y)
      = F y * (if y = x then (Fintype.card H : ℂ) else 0) := by
    intro y
    have h1 : ∀ ψ : AddChar H ℂ, ψ (-x) * (F y * ψ y) = F y * ψ (y + -x) := by
      intro ψ; rw [AddChar.map_add_eq_mul]; ring
    have h2 : ∑ ψ : AddChar H ℂ, ψ (y + -x) = if y = x then (Fintype.card H : ℂ) else 0 := by
      simp [ch_sum_eq, add_neg_eq_zero]
    simp only [h1]
    rw [← Finset.mul_sum, h2]
  rw [Finset.sum_congr rfl (fun y _ => h y)]
  simp [mul_ite, mul_comm]

lemma ch_prod {ι : Type*} (ψ : AddChar H ℂ) (g : ι → H) (s : Finset ι) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma parseval (Q : H → ℝ) :
    ∑ x, (Q x) ^ 2 = (1 / (Fintype.card H : ℝ)) * ∑ ψ : AddChar H ℂ, ‖∑ y, (Q y : ℂ) * ψ y‖ ^ 2 := by
  have hpos : (0 : ℝ) < Fintype.card H := by
    have : Nonempty H := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hQ : ∀ x, (Q x : ℂ) = (1 / (Fintype.card H : ℂ)) * ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, (Q y : ℂ) * ψ y := by
    intro x
    rw [ch_inv]
    field_simp
  have hconj : ∀ ψ : AddChar H ℂ, ∑ x, (Q x : ℂ) * ψ (-x)
      = starRingEnd ℂ (∑ y, (Q y : ℂ) * ψ y) := by
    intro ψ
    simp only [map_sum, map_mul, Complex.conj_ofReal, ← AddChar.inv_apply_eq_conj, AddChar.map_neg_eq_inv]
  have e1 : ∀ x, (Q x : ℂ) ^ 2 = ∑ ψ : AddChar H ℂ, (1 / (Fintype.card H : ℂ)) * ((Q x : ℂ) * ψ (-x)) * ∑ y, (Q y : ℂ) * ψ y := by
    intro x
    calc (Q x : ℂ) ^ 2 = (Q x : ℂ) * ((1 / (Fintype.card H : ℂ)) * ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, (Q y : ℂ) * ψ y) := by
          rw [← hQ x]; ring
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intros; ring
  have e2 : ∀ ψ : AddChar H ℂ, ∑ x, (1 / (Fintype.card H : ℂ)) * ((Q x : ℂ) * ψ (-x)) * ∑ y, (Q y : ℂ) * ψ y
      = (1 / (Fintype.card H : ℂ)) * (starRingEnd ℂ (∑ y, (Q y : ℂ) * ψ y) * ∑ y, (Q y : ℂ) * ψ y) := by
    intro ψ
    rw [← hconj ψ, Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have e3 : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj']; norm_cast
  have key : ((∑ x, (Q x) ^ 2 : ℝ) : ℂ) = (((1 / (Fintype.card H : ℝ)) * ∑ ψ : AddChar H ℂ, ‖∑ y, (Q y : ℂ) * ψ y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
    simp only [e2]
    rw [← Finset.mul_sum]
    simp only [e3]
    push_cast
    rfl
  exact_mod_cast key

end gen
