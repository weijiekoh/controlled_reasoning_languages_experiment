import Mathlib

open Polynomial IntermediateField

/--
Let $f(X)=X^4-X^2-1\in \mathbb{Q}[X]$, $K$ is the splitting field of $f$ over $\mathbb{Q}$,
prove that the number of intermediate fields of $K/\mathbb{Q}$ is 10.
-/
theorem card_intermediateField_splittingField_eq_ten :
    Nat.card (IntermediateField ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField) = 10 := by
  -- group theory part
  have card_sub : ∀ (M : Type) [Group M] [Fintype M] [DecidableEq M],
      Nat.card (Subgroup M) = Fintype.card {s : Finset M // 1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ ∀ a ∈ s, a⁻¹ ∈ s} := by
    intro M _ _ _
    classical
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact
    { toFun := fun H => ⟨Finset.univ.filter (· ∈ H), by simp; intros; exact H.mul_mem ‹_› ‹_›⟩
      invFun := fun s => { carrier := {x | x ∈ s.1}, mul_mem' := fun ha hb => s.2.2.1 _ ha _ hb, one_mem' := s.2.1, inv_mem' := fun ha => s.2.2.2 _ ha }
      left_inv := fun H => by ext x; simp
      right_inv := fun s => by ext x; simp }
  have d4 : Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
    rw [card_sub]; decide
  have hψ : ∃ ψ : DihedralGroup 4 →* Equiv.Perm (Fin 4), Function.Injective ψ ∧
      (∀ σ : Equiv.Perm (Fin 4), σ * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * σ → ∃ x, ψ x = σ) := by
    refine ⟨MonoidHom.mk' (fun x : DihedralGroup 4 => match x with
      | .r i => (Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ i.val
      | .sr i => Equiv.swap 0 1 * (Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ i.val) (by decide), by decide, by decide⟩
  have card_sub_equiv : ∀ {G H : Type} [Group G] [Group H] (e : G ≃* H),
      Nat.card (Subgroup G) = Nat.card (Subgroup H) := by
    intro G H _ _ e
    apply Nat.card_congr
    exact
    { toFun := Subgroup.map e.toMonoidHom
      invFun := Subgroup.map e.symm.toMonoidHom
      left_inv := fun K => by
        ext x; simp [Subgroup.mem_map]
      right_inv := fun K => by
        ext x; simp [Subgroup.mem_map] }
  have grp_main : ∀ (G : Type) [Group G] [Finite G] (f : G →* Equiv.Perm (Fin 4)), Function.Injective f →
      (∀ g, f g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * f g) →
      8 ≤ Nat.card G → Nat.card (Subgroup G) = 10 := by
    intro G _ _ f hf hc hG
    obtain ⟨ψ, ψinj, ψrange⟩ := hψ
    have hmem : ∀ g, f g ∈ ψ.range := fun g => by
      obtain ⟨x, hx⟩ := ψrange (f g) (hc g)
      exact ⟨x, hx⟩
    let k : G →* DihedralGroup 4 :=
      ((MonoidHom.ofInjective ψinj).symm : ψ.range →* DihedralGroup 4).comp
        (f.codRestrict ψ.range hmem)
    have kinj : Function.Injective k := by
      intro a b h
      apply hf
      have := (MonoidHom.ofInjective ψinj).symm.injective h
      simpa using congrArg Subtype.val this
    have hD : Nat.card (DihedralGroup 4) = 8 := by
      rw [Nat.card_eq_fintype_card]; decide
    have hle : Nat.card G ≤ 8 := by
      rw [← hD]; exact Nat.card_le_card_of_injective k kinj
    have kb : Function.Bijective k := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨kinj, by rw [hD]; omega⟩
    rw [card_sub_equiv (MulEquiv.ofBijective k kb), d4]
  -- irreducibility
  have sq5 : ∀ y : ℚ, y ^ 2 ≠ 5 := by
    intro y
    have h5 : IsSquare ((5:ℕ):ℚ) := ⟨y, by push_cast; nlinarith⟩
    have := Rat.isSquare_natCast_iff.mp h5
    obtain ⟨m, hm⟩ := this
    have : m ≤ 3 := by nlinarith
    interval_cases m <;> omega
  
