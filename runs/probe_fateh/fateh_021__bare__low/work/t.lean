import Mathlib

abbrev G := ZMod 3 × ZMod 9

def good (p : G × G) : Prop := 3 • p.1 = 0 ∧ Function.Bijective (fun z : G => z.1.val • p.1 + z.2.val • p.2)

instance : DecidablePred good := fun p => by unfold good; infer_instance

lemma gen (f : G →+ G) (z : G) : f z = z.1.val • f (1,0) + z.2.val • f (0,1) := by
  have : z = z.1.val • ((1:ZMod 3),(0:ZMod 9)) + z.2.val • ((0:ZMod 3),(1:ZMod 9)) := by
    ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_nsmul, map_nsmul]

lemma modsmul {n : ℕ} (a : G) (h : n • a = 0) (m : ℕ) : (m % n) • a = m • a := by
  conv_rhs => rw [← Nat.mod_add_div m n, add_smul, mul_comm, mul_smul, h]
  simp

def mk (a b : G) (h : 3 • a = 0) : G →+ G where
  toFun z := z.1.val • a + z.2.val • b
  map_zero' := by simp
  map_add' x y := by
    have h9 : ∀ b : G, 9 • b = 0 := by decide
    have e1 := modsmul a h (x.1.val + y.1.val)
    have e2 := modsmul b (h9 b) (x.2.val + y.2.val)
    simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add, e1, e2, add_smul]
    abel

lemma card_good : Fintype.card {p // good p} = 108 := by
  rw [Fintype.card_subtype]; decide +kernel

theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  have : Nat.card (AddAut G) = Nat.card {p // good p} := by
    apply Nat.card_congr
    refine
      { toFun := fun f => ⟨(f.toAddMonoidHom (1,0), f.toAddMonoidHom (0,1)), ?_, ?_⟩
        invFun := fun p => AddEquiv.ofBijective (mk p.1.1 p.1.2 p.2.1) p.2.2
        left_inv := ?_
        right_inv := ?_ }
    · have : (3:ℕ) • ((1:ZMod 3),(0:ZMod 9)) = 0 := by decide
      show 3 • f ((1:ZMod 3),(0:ZMod 9)) = 0
      rw [← map_nsmul, this, map_zero]
    · have h := fun z => gen f.toAddMonoidHom z
      simp only [AddEquiv.coe_toAddMonoidHom] at h
      show Function.Bijective (fun z : G => z.1.val • f ((1:ZMod 3),(0:ZMod 9)) + z.2.val • f ((0:ZMod 3),(1:ZMod 9)))
      have : (fun z : G => z.1.val • f ((1:ZMod 3),(0:ZMod 9)) + z.2.val • f ((0:ZMod 3),(1:ZMod 9))) = f := by
        funext z; exact (h z).symm
      rw [this]; exact f.bijective
    · intro f
      apply AddEquiv.ext; intro z
      exact (gen f.toAddMonoidHom z).symm
    · rintro ⟨⟨a, b⟩, h3, hb⟩
      apply Subtype.ext
      have e1 : (1:ZMod 3).val = 1 := rfl
      have e2 : (1:ZMod 9).val = 1 := rfl
      show (mk a b h3 (1,0), mk a b h3 (0,1)) = (a,b)
      have e0 : (0:ZMod 3).val = 0 := rfl
      have e3 : (0:ZMod 9).val = 0 := rfl
      simp only [mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk, e0, e1, e2, e3, one_smul, zero_smul, add_zero, zero_add]
  rw [this, Nat.card_eq_fintype_card, card_good]
