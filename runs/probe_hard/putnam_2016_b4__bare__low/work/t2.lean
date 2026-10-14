
def hh {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) (f : Fin m × Fin m → Bool) : ℝ :=
  vv (f (σ i, i)) - vv (f (i, σ i))

lemma inv_case {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (σ i) = i) (hf : ∀ i, σ i ≠ i) :
    ∀ k : ℕ, ∀ s : Finset (Fin m), s.card = 2 * k → (∀ i ∈ s, σ i ∈ s) →
      ∑ f : Fin m × Fin m → Bool, ∏ i ∈ s, hh σ i f = 2 ^ (m * m) * (-1/2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro s hs _
    have : s = ∅ := Finset.card_eq_zero.mp (by simpa using hs)
    subst this
    simp
  | succ k ih =>
    intro s hs hcl
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨i, hi⟩ := hne
    have hσi : σ i ∈ s.erase i := Finset.mem_erase.mpr ⟨hf i, hcl i hi⟩
    set s' := (s.erase i).erase (σ i) with hs'
    have hcard : s'.card = 2 * k := by
      rw [hs', Finset.card_erase_of_mem hσi, Finset.card_erase_of_mem hi]; omega
    have hmem : ∀ j ∈ s', j ≠ i ∧ j ≠ σ i ∧ σ j ≠ i ∧ σ j ≠ σ i := by
      intro j hj
      simp only [hs', Finset.mem_erase] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      refine ⟨h2, h1, ?_, ?_⟩
      · intro h; apply h1; rw [← h, hσ]
      · intro h; apply h2; exact σ.injective h
    have hcl' : ∀ j ∈ s', σ j ∈ s' := by
      intro j hj
      obtain ⟨a, b, c, d⟩ := hmem j hj
      simp only [hs', Finset.mem_erase]
      exact ⟨d, c, hcl j (by simp only [hs', Finset.mem_erase] at hj; exact hj.2.2)⟩
    have hprod : ∀ f, ∏ j ∈ s, hh σ j f = (hh σ i f * hh σ (σ i) f) * ∏ j ∈ s', hh σ j f := by
      intro f
      rw [← Finset.mul_prod_erase s _ hi, ← Finset.mul_prod_erase (s.erase i) _ hσi, mul_assoc]
    have hpq : ((i, σ i) : Fin m × Fin m) ≠ (σ i, i) := by
      intro h; exact hf i (Prod.mk.inj h).1.symm
    have key := two_coord (i, σ i) (σ i, i) hpq
      (fun b c => (vv c - vv b) * (vv b - vv c))
      (fun f => ∏ j ∈ s', hh σ j f) (by
        intro f b c
        apply Finset.prod_congr rfl
        intro j hj
        obtain ⟨a1, a2, a3, a4⟩ := hmem j hj
        unfold hh
        rw [Function.update_of_ne, Function.update_of_ne, Function.update_of_ne, Function.update_of_ne]
        all_goals simp [Prod.ext_iff, *, Ne.symm]
        )
    simp only [hprod]
    have e1 : ∀ f : Fin m × Fin m → Bool, (hh σ i f * hh σ (σ i) f) =
        (fun b c => (vv c - vv b) * (vv b - vv c)) (f (i, σ i)) (f (σ i, i)) := by
      intro f; simp [hh, hσ]
    simp only [e1]
    rw [key, ih s' hcard hcl']
    have : ∑ b : Bool, ∑ c : Bool, (vv c - vv b) * (vv b - vv c) = -2 := by
      simp [vv]; norm_num
    rw [this]
    rw [pow_succ]; ring
