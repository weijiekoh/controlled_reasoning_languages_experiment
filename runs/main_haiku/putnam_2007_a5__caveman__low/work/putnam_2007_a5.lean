import Mathlib

open Set Nat

theorem putnam_2007_a5
(G : Type*) [Group G] [Fintype G]
(p n : ℕ)
(hp : Nat.Prime p)
(hn : n = {g : G | orderOf g = p}.encard)
: n = 0 ∨ p ∣ (n + 1) := by
  classical
  rcases eq_or_ne n 0 with h0 | h0
  · exact Or.inl h0
  right
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have : Fact (Nat.Prime (m + 1)) := ⟨hp⟩
  have hm : m ≠ 0 := by have := hp.one_lt; omega
  have hne : {g : G | orderOf g = m + 1}.Nonempty := by
    rw [← Set.encard_pos, ← hn]
    exact_mod_cast Nat.pos_of_ne_zero h0
  obtain ⟨g0, hg0⟩ := hne
  have hdvdG : (m + 1) ∣ Fintype.card G := by
    rw [← (show orderOf g0 = m + 1 from hg0)]
    exact orderOf_dvd_card
  have hS : {g : G | orderOf g = m + 1} = {g : G | g ^ (m + 1) = 1} \ {1} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← h]; exact pow_orderOf_eq_one g
      · intro h1
        subst h1
        rw [orderOf_one] at h
        have := hp.one_lt
        omega
    · rintro ⟨h1, h2⟩
      exact orderOf_eq_prime h1 h2
  have one_mem : (1 : G) ∈ {g : G | g ^ (m + 1) = 1} := by
    simp
  have hT : (n : ℕ∞) + 1 = {g : G | g ^ (m + 1) = 1}.encard := by
    rw [hn, hS, Set.encard_sdiff_singleton_add_one one_mem]
  have hTfin : ({g : G | g ^ (m + 1) = 1}).encard
      = ((Nat.card {g : G // g ^ (m + 1) = 1} : ℕ) : ℕ∞) := by
    rw [← Set.Finite.cast_ncard_eq (Set.toFinite _)]
    congr 1
  have hN : n + 1 = Nat.card {g : G // g ^ (m + 1) = 1} := by
    have : ((n + 1 : ℕ) : ℕ∞) = ((Nat.card {g : G // g ^ (m + 1) = 1} : ℕ) : ℕ∞) := by
      push_cast; rw [hT, hTfin]
    exact_mod_cast this
  rw [hN]
  let α := {v : Fin (m + 1) → G // (List.ofFn v).prod = 1}
  have rot_prod : ∀ v : Fin (m + 1) → G, (List.ofFn v).prod = 1 →
      (List.ofFn (fun i => v (i + 1))).prod = 1 := by
    intro v hv
    have hrot : List.ofFn (fun i : Fin (m + 1) => v (i + 1)) = (List.ofFn v).rotate 1 := by
      apply List.ext_getElem
      · simp
      · intro k h1 h2
        simp only [List.getElem_ofFn, List.getElem_rotate, List.length_ofFn]
        congr 1
        apply Fin.ext
        simp [Fin.val_add]
    rw [hrot, List.ofFn_succ, List.rotate_cons_succ, List.rotate_zero, List.prod_append,
      List.prod_singleton]
    rw [List.ofFn_succ, List.prod_cons] at hv
    rw [eq_inv_of_mul_eq_one_right hv, inv_mul_cancel]
  let f : Function.End α := fun v => ⟨fun i => v.1 (i + 1), rot_prod v.1 v.2⟩
  open Fin.NatCast in
  have hcoord : ∀ (k : ℕ) (v : α) (i : Fin (m + 1)),
      (f^[k] v).1 i = v.1 (i + (k : Fin (m + 1))) := by
    intro k
    induction k with
    | zero => intro v i; show v.1 i = v.1 (i + ((0 : ℕ) : Fin (m + 1))); simp
    | succ k ih =>
      intro v i
      rw [Function.iterate_succ_apply']
      show (f^[k] v).1 (i + 1) = _
      rw [ih]
      rw [Nat.cast_succ, show i + 1 + (k : Fin (m + 1)) = i + ((k : Fin (m + 1)) + 1) by rw [add_assoc, add_comm (1 : Fin (m + 1))]]
  open Fin.NatCast in
  have hpow : f ^ (m + 1) ^ 1 = 1 := by
    rw [pow_one]
    funext v
    change f^[m + 1] v = v
    apply Subtype.ext
    funext i
    rw [hcoord]
    have : ((m + 1 : ℕ) : Fin (m + 1)) = 0 := by simp
    rw [this, add_zero]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := m + 1) (n := 1) hpow
  open Fin.NatCast in
  have hrot_const : ∀ v : Fin (m + 1) → G, (∀ j, v (j + 1) = v j) → ∀ i, v i = v 0 := by
    intro v hv i
    have hk : ∀ k : ℕ, v (k : Fin (m + 1)) = v 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.cast_succ, hv, ih]
    have := hk i.val
    rwa [Fin.cast_val_eq_self] at this
  have hfixc : ∀ x : ↑(Function.fixedPoints f), ∀ i, x.1.1 i = x.1.1 0 := by
    intro x i
    have hf : f x.1 = x.1 := x.2
    have hv' : ∀ j, x.1.1 (j + 1) = x.1.1 j := fun j => congrArg (fun w => w.1 j) hf
    exact hrot_const _ hv' i
  have hconst : ∀ c : G, (List.ofFn (fun _ : Fin (m + 1) => c)).prod = c ^ (m + 1) := by
    intro c
    rw [List.ofFn_const, List.prod_replicate, _root_.pow_succ']
  let e2 : ↑(Function.fixedPoints f) ≃ {g : G // g ^ (m + 1) = 1} :=
    { toFun := fun x => ⟨x.1.1 0, by
        have h := x.1.2
        have hc : x.1.1 = fun _ => x.1.1 0 := funext (hfixc x)
        rw [hc, hconst] at h
        exact h⟩
      invFun := fun g => ⟨⟨fun _ => g.1, by
          rw [List.ofFn_const, List.prod_replicate]
          exact g.2⟩, by
          show f _ = _
          exact Subtype.ext (funext fun i => rfl)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (funext fun i => (hfixc x i).symm))
      right_inv := fun g => Subtype.ext rfl }
  have hlast : ∀ v : α, v.1 (Fin.last m) = ((List.ofFn fun i => v.1 i.castSucc).prod)⁻¹ := by
    intro v
    have h := v.2
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton] at h
    exact eq_inv_of_mul_eq_one_right h
  let e1 : α ≃ (Fin m → G) :=
    { toFun := fun v i => v.1 i.castSucc
      invFun := fun w => ⟨Fin.snoc (α := fun _ => G) w ((List.ofFn w).prod)⁻¹, by
          rw [List.ofFn_succ']
          simp [List.concat_eq_append, List.prod_append]⟩
      left_inv := fun v => by
          apply Subtype.ext
          funext i
          induction i using Fin.lastCases with
          | last => simp only [Fin.snoc_last]; exact (hlast v).symm
          | cast i => simp only [Fin.snoc_castSucc]
      right_inv := fun w => by
          funext i
          simp }
  have hcardα : (m + 1) ∣ Fintype.card α := by
    rw [Fintype.card_congr e1, Fintype.card_fun, Fintype.card_fin]
    exact dvd_pow hdvdG hm
  have hfix : (m + 1) ∣ Fintype.card ↑(Function.fixedPoints f) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcardα))
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e2]
  exact hfix
