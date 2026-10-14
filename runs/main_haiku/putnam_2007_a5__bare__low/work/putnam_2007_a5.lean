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
  have : Fact p.Prime := ⟨hp⟩
  have hset : {g : G | orderOf g = p} = ↑(Finset.univ.filter (fun g : G => orderOf g = p)) := by
    ext; simp
  rw [hset, Set.encard_coe_eq_coe_finsetCard] at hn
  have hn' : n = (Finset.univ.filter (fun g : G => orderOf g = p)).card := by exact_mod_cast hn
  have hSF : Finset.univ.filter (fun g : G => g ^ p = 1)
      = insert 1 (Finset.univ.filter (fun g : G => orderOf g = p)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases h1 : g = 1
      · exact Or.inl h1
      · exact Or.inr (orderOf_eq_prime h h1)
    · rintro (rfl | h)
      · exact one_pow p
      · rw [← h]; exact pow_orderOf_eq_one g
  have h1notin : (1:G) ∉ Finset.univ.filter (fun g : G => orderOf g = p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, orderOf_one]
    exact hp.one_lt.ne
  have hScard : (Finset.univ.filter (fun g : G => g ^ p = 1)).card = n + 1 := by
    rw [hSF, Finset.card_insert_of_notMem h1notin, hn']
  -- key divisibility
  have key : p ∣ Fintype.card G → p ∣ (Finset.univ.filter (fun g : G => g ^ p = 1)).card := by
    intro hd
    let T := {v : List.Vector G p // v.toList.prod = 1}
    let f : T → T := fun x =>
      ⟨⟨x.1.toList.rotate 1, by simp⟩, List.prod_rotate_eq_one_of_prod_eq_one x.2 1⟩
    have hiter : ∀ (k : ℕ) (x : T), ((f^[k]) x).1.toList = x.1.toList.rotate k := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply']
        have h1 : (f (f^[k] x)).1.toList = ((f^[k] x).1.toList).rotate 1 := rfl
        rw [h1, ih, List.rotate_rotate]
    let F : Function.End T := f
    have hpow : ∀ (k : ℕ) (x : T), (F^k) x = f^[k] x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
        intro x
        rw [pow_succ, Function.End.mul_def]
        show (F^k) (f x) = _
        rw [ih, Function.iterate_succ_apply]
    have hf : F ^ (p ^ 1) = 1 := by
      refine funext fun x => ?_
      rw [hpow, pow_one]
      show f^[p] x = x
      have h : (f^[p] x).1.toList = x.1.toList := by
        rw [hiter]
        have h2 : x.1.toList.rotate p = x.1.toList.rotate x.1.toList.length :=
          congrArg (fun m => x.1.toList.rotate m) x.1.2.symm
        rw [h2]
        exact List.rotate_length _
      exact Subtype.ext (Subtype.ext h)
    have hmod := @Equiv.Perm.card_fixedPoints_modEq T _ _ F p 1 _ hf
    let R : {g : G // g ^ p = 1} → T := fun a =>
      ⟨⟨List.replicate p a.1, by simp⟩, by show (List.replicate p a.1).prod = 1; rw [List.prod_replicate]; exact a.2⟩
    have hRfix : ∀ a, F (R a) = R a := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact List.rotate_replicate _ _ _
    have hp0 : p ≠ 0 := hp.ne_zero
    have hfix : Fintype.card ↑(Function.fixedPoints F) = (Finset.univ.filter (fun g : G => g ^ p = 1)).card := by
      rw [← Fintype.card_subtype]; symm
      refine Fintype.card_of_bijective (f := fun a => (⟨R a, hRfix a⟩ : ↑(Function.fixedPoints F))) ⟨?_, ?_⟩
      · intro a b hab
        have h1 : R a = R b := congrArg Subtype.val hab
        have h2 : List.replicate p a.1 = List.replicate p b.1 := congrArg (fun y : T => y.1.toList) h1
        have h3 : a.1 ∈ List.replicate p b.1 := by
          rw [← h2, List.mem_replicate]; exact ⟨hp0, rfl⟩
        rw [List.mem_replicate] at h3
        exact Subtype.ext h3.2
      · rintro ⟨y, hy⟩
        have hy' : F y = y := hy
        have h : y.1.toList.rotate 1 = y.1.toList := congrArg (fun z : T => z.1.toList) hy'
        have h' : ∀ n, y.1.toList.rotate n = y.1.toList := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [← List.rotate_rotate, ih, h]
        obtain ⟨a, ha⟩ := List.rotate_eq_self_iff_eq_replicate.1 h'
        have hl : y.1.toList.length = p := y.1.2
        have hap : a ^ p = 1 := by
          have : (List.replicate y.1.toList.length a).prod = 1 := by
            rw [← ha]; exact y.2
          rw [List.prod_replicate, hl] at this
          exact this
        refine ⟨⟨a, hap⟩, ?_⟩
        have hfin : List.replicate p a = y.1.toList := by rw [ha, hl]
        exact Subtype.ext (Subtype.ext (Subtype.ext hfin))
    have hTcard : Fintype.card T = Fintype.card G ^ (p - 1) := by
      have hlen : ∀ w : List.Vector G (p - 1), (w.toList ++ [(w.toList.prod)⁻¹]).length = p := by
        intro w
        have h2 := hp.two_le
        have h3 : w.toList.length = p - 1 := w.2
        simp only [List.length_append, List.length_singleton]
        omega
      have hprod : ∀ w : List.Vector G (p - 1), (w.toList ++ [(w.toList.prod)⁻¹]).prod = 1 := by
        intro w
        simp [List.prod_append]
      let phi : List.Vector G (p - 1) → T := fun w => ⟨⟨w.toList ++ [(w.toList.prod)⁻¹], hlen w⟩, hprod w⟩
      have hbij : Function.Bijective phi := by
        constructor
        · intro w w' h
          have h1 : w.toList ++ [(w.toList.prod)⁻¹] = w'.toList ++ [(w'.toList.prod)⁻¹] :=
            congrArg (fun z : T => z.1.toList) h
          have h2 : w.toList = w'.toList := (List.append_inj' h1 rfl).1
          exact Subtype.ext h2
        · intro v
          set L := v.1.toList with hL
          have hLlen : L.length = p := v.1.2
          have hdrop : (L.drop (p - 1)).length = 1 := by
            simp only [List.length_drop, hLlen]
            have := hp.two_le
            omega
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hdrop
          have hsplit : L = L.take (p - 1) ++ [x] := by
            have := List.take_append_drop (p - 1) L
            rw [hx] at this
            exact this.symm
          have hv : (L.take (p - 1)).prod * x = 1 := by
            have h1 : L.prod = 1 := v.2
            rw [hsplit, List.prod_append, List.prod_singleton] at h1
            exact h1
          have hxval : x = ((L.take (p - 1)).prod)⁻¹ := eq_inv_of_mul_eq_one_right hv
          refine ⟨⟨L.take (p - 1), by simp only [List.length_take, hLlen]; omega⟩, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          show L.take (p - 1) ++ [((L.take (p - 1)).prod)⁻¹] = L
          rw [← hxval]
          exact hsplit.symm
      rw [← Fintype.card_of_bijective hbij]
      simp
    have hpT : p ∣ Fintype.card T := by
      rw [hTcard]
      exact dvd_pow hd (by have := hp.two_le; omega)
    rw [← hfix]
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpT))
  by_cases hd : p ∣ Fintype.card G
  · right
    rw [← hScard]
    exact key hd
  · left
    rw [hn', Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    apply hd
    rw [← hg]
    exact orderOf_dvd_card
