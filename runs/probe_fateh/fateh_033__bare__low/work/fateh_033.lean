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
  have hf0 : f ≠ 0 := hf'.ne_zero
  have hnd : f.natDegree = n := natDegree_eq_of_degree_eq_some hf
  have hsep : f.Separable := hf'.separable
  have hcard : Nat.card f.Gal = n.factorial := by
    rw [Nat.card_congr h.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have trans : ∀ c d : SplittingField f, f.aeval c = 0 → f.aeval d = 0 → ∃ σ : f.Gal, σ c = d := by
    intro c d hc hd
    have hdv : f ∣ minpoly ℚ d := 
      (Irreducible.dvd_symm (minpoly.irreducible (Algebra.IsIntegral.isIntegral d)) hf')
        (minpoly.dvd ℚ d hd)
    have : aeval c (minpoly ℚ d) = 0 := by
      obtain ⟨g, hg⟩ := hdv
      rw [hg, map_mul]; simp [hc]
    exact minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic d) this
  obtain ⟨τ, hτ⟩ := trans a b ha hb
  have hstab : Nat.card {g : f.Gal // g a = b} = Nat.card (MulAction.stabilizer f.Gal a) := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨τ⁻¹ * g.1, by
          show τ.symm (g.1 a) = a
          rw [g.2, ← hτ]; exact τ.symm_apply_apply a ⟩
        invFun := fun g => ⟨τ * g.1, by
          have h2 : g.1 a = a := g.2
          show τ (g.1 a) = b
          rw [h2, hτ]⟩
        left_inv := fun g => by ext1; simp
        right_inv := fun g => by ext1; simp }
  have horb : Nat.card (MulAction.orbit f.Gal a) = n := by
    have : (MulAction.orbit f.Gal a) = (f.rootSet (SplittingField f) : Set _) := by
      ext c
      simp only [mem_rootSet, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨σ, rfl⟩
        refine ⟨hf0, ?_⟩
        have := aeval_algHom_apply (AlgEquiv.toAlgHom (σ : f.SplittingField ≃ₐ[ℚ] f.SplittingField)) a f
        simp [ha] at this
        exact this
      · rintro ⟨_, hc⟩
        exact trans a c ha hc
    have hc := card_rootSet_eq_natDegree hsep (SplittingField.splits f)
    rw [← Nat.card_eq_fintype_card, hnd] at hc
    rw [this]; exact hc
  haveI : Finite f.Gal := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Fintype f.Gal := Fintype.ofFinite _
  haveI : Finite (MulAction.orbit f.Gal a) := Finite.of_surjective (fun g : f.Gal => (⟨g • a, g, rfl⟩ : MulAction.orbit f.Gal a)) (by rintro ⟨_, g, rfl⟩; exact ⟨g, rfl⟩)
  haveI : Fintype (MulAction.orbit f.Gal a) := Fintype.ofFinite _
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group f.Gal a
  simp only [← Nat.card_eq_fintype_card] at key
  rw [horb, hcard, ← hstab] at key
  have hn' : n.factorial = n * (n-1).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
    simp [Nat.factorial_succ]
  rw [hn'] at key
  exact Nat.eq_of_mul_eq_mul_left (by omega) key
