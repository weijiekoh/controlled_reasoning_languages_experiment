
lemma zero_case {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : ¬ (∀ i, σ (σ i) = i ∧ σ i ≠ i)) :
    ∑ f : Fin m × Fin m → Bool, ∏ i, hh σ i f = 0 := by
  by_cases hfix : ∃ i, σ i = i
  · obtain ⟨i, hi⟩ := hfix
    apply Finset.sum_eq_zero; intro f _
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hh, hi]
  · push_neg at hfix
    have : ∃ i, σ (σ i) ≠ i := by
      by_contra hc; push_neg at hc
      exact h (fun i => ⟨hc i, hfix i⟩)
    obtain ⟨i, hi⟩ := this
    set p : Fin m × Fin m := (i, σ i)
    set q : Fin m × Fin m := (σ i, i)
    let e : (Fin m × Fin m → Bool) ≃ (Fin m × Fin m → Bool) :=
      Equiv.arrowCongr (Equiv.swap p q) (Equiv.refl Bool)
    have he : ∀ f x, e f x = f (Equiv.swap p q x) := by
      intro f x; simp [e, Equiv.arrowCongr, Equiv.symm_swap]
    have hother : ∀ j, j ≠ i → ∏ _x ∈ ({j} : Finset (Fin m)), (1:ℝ) = 1 := by intros; simp
    have hj' : ∀ f, ∀ j, j ≠ i → hh σ j (e f) = hh σ j f := by
      intro f j hji
      unfold hh
      rw [he, he]
      have a1 : Equiv.swap p q (σ j, j) = (σ j, j) := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; simp only [p, Prod.ext_iff] at h
          apply hi; rw [← h.2]; exact h.1
        · intro h; simp only [q, Prod.ext_iff] at h
          exact hji h.2
      have a2 : Equiv.swap p q (j, σ j) = (j, σ j) := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; simp only [p, Prod.ext_iff] at h
          exact hji h.1
        · intro h; simp only [q, Prod.ext_iff] at h
          apply hi; rw [← h.1]; exact h.2
      rw [a1, a2]
    have hi' : ∀ f, hh σ i (e f) = - hh σ i f := by
      intro f
      unfold hh
      rw [he, he]
      have hpq : p ≠ q := by
        intro h; simp only [p, q, Prod.ext_iff] at h; exact hfix i h.1.symm
      have a1 : Equiv.swap p q (σ i, i) = p := Equiv.swap_apply_right p q
      have a2 : Equiv.swap p q (i, σ i) = q := Equiv.swap_apply_left p q
      rw [a1, a2]; simp only [p, q]; ring
    have hprod : ∀ f, ∏ j, hh σ j (e f) = - ∏ j, hh σ j f := by
      intro f
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ (fun j => hh σ j f) (Finset.mem_univ i), hi']
      rw [Finset.prod_congr rfl (fun j hj => hj' f j (Finset.ne_of_mem_erase hj))]
      ring
    have := Equiv.sum_comp e (fun f => ∏ j, hh σ j f)
    simp only [hprod, Finset.sum_neg_distrib] at this
    linarith
