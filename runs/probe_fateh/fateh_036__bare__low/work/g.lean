import Mathlib
open Equiv

theorem card_sub (M : Type) [Group M] [Fintype M] [DecidableEq M] :
    Nat.card (Subgroup M) = Fintype.card {s : Finset M // 1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ ∀ a ∈ s, a⁻¹ ∈ s} := by
  classical
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
  { toFun := fun H => ⟨Finset.univ.filter (· ∈ H), by simp [H.mul_mem, H.inv_mem]; intros; exact H.mul_mem ‹_› ‹_›⟩
    invFun := fun s => { carrier := {x | x ∈ s.1}, mul_mem' := fun ha hb => s.2.2.1 _ ha _ hb, one_mem' := s.2.1, inv_mem' := fun ha => s.2.2.2 _ ha }
    left_inv := fun H => by ext x; simp
    right_inv := fun s => by ext x; simp }

theorem d4 : Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
  rw [card_sub]; decide
