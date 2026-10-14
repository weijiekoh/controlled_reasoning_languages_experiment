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
open Equiv

def τ : Perm (Fin 4) := swap 0 1 * swap 2 3
def ρ : Perm (Fin 4) := swap 0 2 * swap 2 1 * swap 1 3
def ψf : DihedralGroup 4 → Perm (Fin 4)
  | .r i => ρ ^ i.val
  | .sr i => swap 0 1 * ρ ^ i.val

def ψ : DihedralGroup 4 →* Perm (Fin 4) :=
  MonoidHom.mk' ψf (by decide)

theorem ψinj : Function.Injective ψ := by decide

theorem ψrange : ∀ σ : Perm (Fin 4), σ * τ = τ * σ → ∃ x, ψ x = σ := by decide
theorem ψcomm : ∀ x, ψ x * τ = τ * ψ x := by decide

theorem card_sub_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup G) = Nat.card (Subgroup H) := by
  apply Nat.card_congr
  exact
  { toFun := Subgroup.map e.toMonoidHom
    invFun := Subgroup.map e.symm.toMonoidHom
    left_inv := fun K => by
      ext x; simp [Subgroup.mem_map]
    right_inv := fun K => by
      ext x; simp [Subgroup.mem_map] }

theorem grp_main (G : Type) [Group G] [Finite G] (f : G →* Perm (Fin 4)) (hf : Function.Injective f)
    (hc : ∀ g, f g * τ = τ * f g) (hG : Nat.card G = 8) : Nat.card (Subgroup G) = 10 := by
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
  have kb : Function.Bijective k := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨kinj, by rw [hG, hD]⟩
  rw [card_sub_equiv (MulEquiv.ofBijective k kb), d4]
