import Mathlib

open Polynomial

/--
Let $f(x) \in \mathbb{Q}[x]$ be a polynomial of degree $n$ ($n>4$) and the splitting field $E$
of $f(x)$ has Galois group $S_n$ over $\mathbb{Q}$. Let $\alpha$ be a zero of $f(x)$ in $E$.
Prove that for any other root $\beta$ of $f(x)$, there are precisely $(n-1)!$ elements in
$\mathrm{Gal}(E/\mathbb{Q})$ that takes $\alpha $ to $\beta$
-/
theorem card_gal_map_eq_eq_factorial {n : Nat} (hn : n > 4) (f : ℚ[X]) (hf : f.degree = n)
    (hf' : Irreducible f) (h : f.Gal ≃* (Equiv.Perm <| Fin n))
    {a b : SplittingField f} (ha : f.aeval a = 0) (hb : f.aeval b = 0) (neq : a ≠ b) :
    Nat.card {h : f.Gal // h a = b} = Nat.factorial (n - 1) := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have hcard : Nat.card (f.rootSet f.SplittingField) = n := by
    rw [Nat.card_eq_fintype_card]
    exact (card_rootSet_eq_natDegree hf'.separable (SplittingField.splits f)).trans (natDegree_eq_of_degree_eq_some hf)
  have hG : Nat.card f.Gal = n.factorial := by
    rw [Nat.card_congr h.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hpt : MulAction.IsPretransitive f.Gal (f.rootSet f.SplittingField) := by
    haveI : Fact (map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
    convert Polynomial.Gal.galAction_isPretransitive f f.SplittingField hf'
    rfl
  have := hpt
  let a' : f.rootSet f.SplittingField := ⟨a, mem_rootSet.2 ⟨hf0, ha⟩⟩
  let b' : f.rootSet f.SplittingField := ⟨b, mem_rootSet.2 ⟨hf0, hb⟩⟩
  have horb : MulAction.orbit f.Gal a' = Set.univ := MulAction.orbit_eq_univ _ _
  have hmem : b' ∈ MulAction.orbit f.Gal a' := by rw [horb]; trivial
  obtain ⟨σ0, hσ⟩ := hmem
  have hσ' : σ0 • a' = b' := hσ
  have key : ∀ σ : f.Gal, (σ • a').1 = σ a := fun σ => rfl
  have hfib : Nat.card {g : f.Gal // g a = b} = Nat.card (MulAction.stabilizer f.Gal a') := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨σ0⁻¹ * g.1, by
          rw [MulAction.mem_stabilizer_iff, mul_smul]
          have hg' : g.1 • a' = b' := Subtype.ext ((key g.1).trans g.2)
          rw [hg', ← hσ, inv_smul_smul]⟩
        invFun := fun k => ⟨σ0 * k.1, by
          have hk := MulAction.mem_stabilizer_iff.1 k.2
          have hk' : (σ0 * k.1) • a' = b' := by
            rw [mul_smul, hk, hσ']
          exact (key _).symm.trans (congrArg Subtype.val hk')⟩
        left_inv := fun g => by
          apply Subtype.ext
          simp
        right_inv := fun k => by
          apply Subtype.ext
          simp }
  have hidx := MulAction.index_stabilizer f.Gal a'
  have hprod := Subgroup.card_mul_index (MulAction.stabilizer f.Gal a')
  rw [hidx, horb, Set.ncard_univ, hcard, hG] at hprod
  rw [hfib]
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n := by omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [Nat.mul_factorial_pred hn0, ← hprod, Nat.mul_comm]
