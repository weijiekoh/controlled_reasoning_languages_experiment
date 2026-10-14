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
  have hdeg : f.natDegree = n := natDegree_eq_of_degree_eq_some hf
  have : Fact (Polynomial.map (algebraMap ℚ (SplittingField f)) f).Splits :=
    ⟨SplittingField.splits f⟩
  have hsep : f.Separable := hf'.separable
  have hcard : Nat.card (f.rootSet (SplittingField f)) = n := by
    have h1 := card_rootSet_eq_natDegree hsep (SplittingField.splits f)
    rw [Fintype.card_eq_nat_card] at h1
    exact h1.trans hdeg
  have key : ∀ (g : f.Gal) (x : f.rootSet (SplittingField f)), (g • x).1 = g x.1 := by
    sorry
  have := Polynomial.Gal.galAction_isPretransitive f (SplittingField f) hf'
  have hGal : Nat.card f.Gal = n.factorial := by
    rw [Nat.card_congr h.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  let A : f.rootSet (SplittingField f) := ⟨a, Polynomial.mem_rootSet.mpr ⟨hf0, ha⟩⟩
  let B : f.rootSet (SplittingField f) := ⟨b, Polynomial.mem_rootSet.mpr ⟨hf0, hb⟩⟩
  obtain ⟨g0, hg0⟩ : ∃ g : f.Gal, g • A = B := MulAction.exists_smul_eq f.Gal A B
  have hg0' : g0 a = b := by
    have h1 := key g0 A
    rw [hg0] at h1
    exact h1.symm
  have hidx : (MulAction.stabilizer f.Gal A).index = n := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, hcard]
  have hfib : Nat.card {h : f.Gal // h a = b} = Nat.card (MulAction.stabilizer f.Gal A) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨g0⁻¹ * x.1, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          rw [key]
          show g0⁻¹ (x.1 a) = a
          rw [x.2, ← hg0']
          exact AlgEquiv.symm_apply_apply g0 a⟩
        invFun := fun s => ⟨g0 * s.1, by
          have hs : s.1 • A = A := (MulAction.mem_stabilizer_iff).mp s.2
          have hs' : s.1 a = a := by
            have h1 := key s.1 A
            rw [hs] at h1
            exact h1.symm
          show g0 (s.1 a) = b
          rw [hs', hg0']⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp
        right_inv := fun s => by
          apply Subtype.ext
          simp }
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer f.Gal A)
  rw [hidx, hGal] at hmul
  rw [hfib]
  have hn0 : 0 < n := by omega
  have : n * Nat.card (MulAction.stabilizer f.Gal A) = n * (n - 1).factorial := by
    rw [hmul, mul_comm, Nat.mul_factorial_pred hn0]
  exact Nat.eq_of_mul_eq_mul_left hn0 this
