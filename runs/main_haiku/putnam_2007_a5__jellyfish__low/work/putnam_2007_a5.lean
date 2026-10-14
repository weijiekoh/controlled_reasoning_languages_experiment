import Mathlib

open Set Nat

/--
Suppose that a finite group has exactly $n$ elements of order $p$, where $p$ is a prime. Prove that either $n = 0$ or $p$ divides $n+1$.
-/
theorem putnam_2007_a5
(G : Type*) [Group G] [Fintype G]
(p n : ℕ)
(hp : Nat.Prime p)
(hn : n = {g : G | orderOf g = p}.encard)
: n = 0 ∨ p ∣ (n + 1) := by
  classical
  haveI := Fact.mk hp
  by_cases hd : p ∣ Fintype.card G
  swap
  · left
    have hempty : ({g : G | orderOf g = p} : Set G) = ∅ := by
      ext g
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hg
      apply hd
      rw [← hg]
      exact orderOf_dvd_card
    have h := hn
    rw [hempty, Set.encard_empty] at h
    exact_mod_cast h
  · right
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    have hk : k ≠ 0 := by have := hp.two_le; omega
    
    obtain ⟨T, hTdef⟩ :∃ T : Finset G, T = Finset.univ.filter (fun g => g ^ (k+1) = 1) := ⟨_, rfl⟩
    have hT : T.card = n + 1 := by
      have hset : ({g : G | orderOf g = k+1} : Set G) = ((Finset.univ.filter (fun g : G => orderOf g = k+1) : Finset G) : Set G) := by
        ext; simp
      have h := hn
      rw [hset, Set.encard_coe_eq_coe_finsetCard] at h
      have hn' : n = (Finset.univ.filter (fun g : G => orderOf g = k+1)).card := by exact_mod_cast h
      have h1 : T = insert 1 (Finset.univ.filter (fun g : G => orderOf g = k+1)) := by
        rw [hTdef]
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h
          by_cases h1 : g = 1
          · left; exact h1
          · right; exact orderOf_eq_prime h h1
        · rintro (rfl | h)
          · simp
          · rw [← h]; exact pow_orderOf_eq_one g
      have h2 : (1:G) ∉ Finset.univ.filter (fun g : G => orderOf g = k+1) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, orderOf_one]
        omega
      rw [h1, Finset.card_insert_of_notMem h2, hn']
    -- |X| = |G|^k, divisible by p
    have hpX : (k+1) ∣ Fintype.card {f : Fin (k+1) → G // (List.ofFn f).prod = 1} := by
      have e : {f : Fin (k+1) → G // (List.ofFn f).prod = 1} ≃ (Fin k → G) :=
        { toFun := fun f i => f.1 i.castSucc
          invFun := fun g => ⟨Fin.snoc g ((List.ofFn g).prod)⁻¹, by
            rw [List.ofFn_succ', List.prod_concat]
            simp [Fin.snoc_castSucc, Fin.snoc_last]⟩
          left_inv := by
            intro f
            apply Subtype.ext
            have hf := f.2
            rw [List.ofFn_succ', List.prod_concat] at hf
            have hl := eq_inv_of_mul_eq_one_right hf
            funext i
            induction i using Fin.lastCases with
            | last => simp [Fin.snoc_last, hl]
            | cast i => simp [Fin.snoc_castSucc]
          right_inv := by
            intro g
            funext i
            simp [Fin.snoc_castSucc] }
      have hcard : Fintype.card {f : Fin (k+1) → G // (List.ofFn f).prod = 1} = Fintype.card G ^ k := by
        rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
      rw [hcard]
      exact dvd_pow hd hk
    -- the rotation
    have hrot : ∀ f : Fin (k+1) → G,
        (List.ofFn (fun i => f (finRotate (k+1) i))).prod = 1 ↔ (List.ofFn f).prod = 1 := by
      intro f
      have e1 : List.ofFn f = f 0 :: List.ofFn (fun i : Fin k => f i.succ) := List.ofFn_succ
      have e2 : List.ofFn (fun i => f (finRotate (k+1) i))
          = (List.ofFn (fun i : Fin k => f i.succ)).concat (f 0) := by
        rw [List.ofFn_succ']
        congr 1
        · congr 1
          funext i
          congr 1
          rw [finRotate_apply]
          exact Fin.coeSucc_eq_succ
        · congr 1
          rw [finRotate_last]
      rw [e2, e1, List.prod_concat, List.prod_cons, mul_eq_one_comm]
    obtain ⟨σ, hσ⟩ : ∃ σ : Function.End {f : Fin (k+1) → G // (List.ofFn f).prod = 1},
        ∀ x i, (σ x).1 i = x.1 (finRotate (k+1) i) :=
      ⟨fun x => ⟨fun i => x.1 (finRotate (k+1) i), (hrot x.1).mpr x.2⟩, fun x i => rfl⟩
    open Fin.NatCast in
    have hiter : ∀ m : ℕ, ∀ x, ∀ i, ((σ ^ m) x).1 i = x.1 (i + (Nat.cast m : Fin (k+1))) := by
      intro m
      induction m with
      | zero => intro x i; rw [pow_zero, Nat.cast_zero, add_zero]; rfl
      | succ m ih =>
        intro x i
        rw [_root_.pow_succ']
        show (σ ((σ ^ m) x)).1 i = _
        rw [hσ, ih, finRotate_apply]
        rw [Nat.cast_succ, add_assoc, add_comm (1 : Fin (k+1))]
    have hpow : σ ^ (k+1) = 1 := by
      have h : ∀ x, (σ ^ (k+1)) x = x := by
        intro x
        apply Subtype.ext
        funext i
        rw [hiter, Fin.natCast_self, add_zero]
      funext x
      exact h x
    -- fixed points ≅ {g | g^(k+1) = 1}
    open Fin.NatCast in
    have hfix : Fintype.card (Function.fixedPoints σ) = T.card := by
      have hconst : ∀ x, σ x = x → ∀ i, x.1 i = x.1 0 := by
        intro x hx
        have h1 : ∀ j, x.1 (finRotate (k+1) j) = x.1 j := by
          intro j; rw [← hσ, hx]
        have h2 : ∀ j : Fin (k+1), x.1 (j + 1) = x.1 j := by
          intro j; have := h1 j; rwa [finRotate_apply] at this
        have h3 : ∀ m : ℕ, x.1 (Nat.cast m : Fin (k+1)) = x.1 0 := by
          intro m
          induction m with
          | zero => simp
          | succ m ih => rw [Nat.cast_succ, h2, ih]
        intro i
        rw [← Fin.cast_val_eq_self i, h3]
      have hmem : ∀ x : Function.fixedPoints σ, x.1.1 0 ∈ T := by
        intro x
        have hx : σ x.1 = x.1 := x.2
        have hc : x.1.1 = fun _ => x.1.1 0 := funext (hconst x.1 hx)
        have hp1 := x.1.2
        rw [hc, List.ofFn_const, List.prod_replicate] at hp1
        rw [hTdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hp1⟩
      have hmemT : ∀ y : G, y ∈ T ↔ y ^ (k+1) = 1 := by
        intro y; rw [hTdef, Finset.mem_filter]; simp
      have hcg : ∀ g : {g : G // g ∈ T}, (List.ofFn (fun _ : Fin (k+1) => g.1)).prod = 1 := by
        intro g
        rw [List.ofFn_const, List.prod_replicate]; exact (hmemT _).mp g.2
      have e : (Function.fixedPoints σ) ≃ {g : G // g ∈ T} :=
        { toFun := fun x => ⟨x.1.1 0, hmem x⟩
          invFun := fun g =>
            ⟨⟨fun _ => g.1, hcg g⟩, by
              show σ _ = _
              exact Subtype.ext (funext fun i => hσ _ i)⟩
          left_inv := by
            intro x
            apply Subtype.ext
            apply Subtype.ext
            funext i
            exact (hconst x.1 x.2 i).symm
          right_inv := by
            intro g
            rfl }
      rw [Fintype.card_congr e, Fintype.card_coe]
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := σ) (p := k+1) (n := 1)
      (by simpa using hpow)
    have hdiv : (k+1) ∣ Fintype.card (Function.fixedPoints σ) := by
      have h0 := hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpX)
      exact Nat.modEq_zero_iff_dvd.mp (by convert h0)
    rw [hfix, hT] at hdiv
    exact hdiv
