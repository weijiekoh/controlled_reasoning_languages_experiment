
lemma char_inv (n : ℕ) (σ : Equiv.Perm (Fin (2*n))) :
    (∀ i, σ (σ i) = i ∧ σ i ≠ i) ↔ σ.cycleType = Multiset.replicate n 2 := by
  constructor
  · intro h
    have hsq : σ ^ 2 = 1 := by
      ext i; simp [pow_two, Equiv.Perm.mul_apply, (h i).1]
    have hsupp : σ.support = Finset.univ := by
      ext i; simp [Equiv.Perm.mem_support, (h i).2]
    have hall : ∀ b ∈ σ.cycleType, b = 2 := by
      intro b hb
      have h1 := Equiv.Perm.dvd_of_mem_cycleType hb
      have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have := Equiv.Perm.two_le_of_mem_cycleType hb
      have := Nat.le_of_dvd (by norm_num) (h1.trans h2)
      omega
    have e := Multiset.eq_replicate_of_mem hall
    have hs := Equiv.Perm.sum_cycleType σ
    rw [hsupp, e] at hs
    simp at hs
    rw [e]
    have : σ.cycleType.card = n := by omega
    rw [this]
  · intro h
    have hs := Equiv.Perm.sum_cycleType σ
    rw [h] at hs
    simp at hs
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simp; omega
    have hlcm := Equiv.Perm.lcm_cycleType σ
    rw [h] at hlcm
    have hord : orderOf σ ∣ 2 := by
      rw [← hlcm]; 
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · apply Multiset.lcm_dvd.mpr; intro b hb; rw [Multiset.eq_of_mem_replicate hb]
    intro i
    have hi : i ∈ σ.support := by rw [hsupp]; simp
    refine ⟨?_, (Equiv.Perm.mem_support.mp hi)⟩
    have : σ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    have := congrArg (fun g => g i) this
    simpa [pow_two, Equiv.Perm.mul_apply] using this

lemma count_inv (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card
      * (2 ^ n * n.factorial) = (2 * n).factorial := by
  have := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2*n)) (Multiset.replicate n 2)
  have h2 : (Multiset.replicate n 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]; simp; omega
  simp [h2] at this
  rw [if_pos ⟨by omega, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩, show 2 * n - n * 2 = 0 by omega] at this
  simpa using this
