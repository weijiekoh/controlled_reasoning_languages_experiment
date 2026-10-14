import Mathlib

noncomputable abbrev putnam_2006_b4_solution : ℕ → ℕ := fun k ↦ 2 ^ k
/--
Let $Z$ denote the set of points in $\mathbb{R}^n$ whose coordinates are $0$ or $1$. (Thus $Z$ has $2^n$ elements, which are the vertices of a unit hypercube in $\mathbb{R}^n$.) Given a vector subspace $V$ of $\mathbb{R}^n$, let $Z(V)$ denote the number of members of $Z$ that lie in $V$. Let $k$ be given, $0 \leq k \leq n$. Find the maximum, over all vector subspaces $V \subseteq \mathbb{R}^n$ of dimension $k$, of the number of points in $V \cap Z$.
-/
theorem putnam_2006_b4
    (n k : ℕ)
    (npos : n > 0)
    (hk : k ≤ n)
    (Z : Set (Fin n → ℝ))
    (hZ : Z = {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1}) :
    IsGreatest
      {y | ∃ V : Subspace ℝ (Fin n → ℝ), Module.rank ℝ V = k ∧ (Z ∩ V).ncard = y}
      (putnam_2006_b4_solution k) :=
  by
  subst hZ
  have aux : ∀ d : ℕ, ∀ W : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ W ≤ d →
      ∃ S : Finset (Fin n), S.card ≤ d ∧ ∀ x ∈ W, (∀ j ∈ S, x j = 0) → x = 0 := by
    intro d
    induction d with
    | zero =>
      intro W hW
      have hb : W = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      refine ⟨∅, by simp, fun x hx _ => ?_⟩
      rw [hb] at hx
      exact (Submodule.mem_bot ℝ).mp hx
    | succ d ih =>
      intro W hW
      by_cases h : ∃ j : Fin n, ∃ x ∈ W, x j ≠ 0
      · obtain ⟨j, x0, hx0, hj⟩ := h
        have hlt : W ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) < W := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro heq
          have hmem : x0 ∈ W ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
            rw [heq]; exact hx0
          have h2 := (Submodule.mem_inf.mp hmem).2
          simp at h2
          exact hj h2
        have hfin := Submodule.finrank_lt_finrank_of_lt hlt
        obtain ⟨S, hS, hinj⟩ := ih (W ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)) (by omega)
        refine ⟨insert j S, ?_, ?_⟩
        · exact (Finset.card_insert_le j S).trans (by omega)
        · intro x hx hzero
          have hxj : x j = 0 := hzero j (Finset.mem_insert_self j S)
          have hxW' : x ∈ W ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
            refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
            simp [hxj]
          exact hinj x hxW' (fun i hi => hzero i (Finset.mem_insert_of_mem hi))
      · push_neg at h
        refine ⟨∅, by simp, fun x hx _ => ?_⟩
        funext j
        exact h j x hx
  constructor
  · obtain ⟨g, hg⟩ : ∃ g : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ),
        ∀ a j, g a j = if h : j.val < k then a ⟨j.val, h⟩ else 0 :=
      ⟨{ toFun := fun a j => if h : j.val < k then a ⟨j.val, h⟩ else 0
         map_add' := by
           intro a b; funext j; by_cases h : j.val < k <;> simp [h]
         map_smul' := by
           intro c a; funext j; by_cases h : j.val < k <;> simp [h] },
       fun a j => rfl⟩
    have hinjg : Function.Injective g := by
      intro a b hab
      funext i
      have h1 := congrFun hab (Fin.castLE hk i)
      rw [hg, hg, dif_pos (by simp), dif_pos (by simp)] at h1
      exact h1
    have hfinr : Module.finrank ℝ (LinearMap.range g) = k := by
      rw [LinearMap.finrank_range_of_inj hinjg]
      simp
    have hrank : Module.rank ℝ (LinearMap.range g) = k := by
      rw [← Module.finrank_eq_rank, hfinr]
    have hfinj : Function.Injective (fun b : Fin k → Bool => g (fun i => if b i then (1:ℝ) else 0)) := by
      intro b c hbc
      have h2 := hinjg hbc
      funext i
      have h3 := congrFun h2 i
      cases hb : b i <;> cases hc : c i <;> simp [hb, hc] at h3 ⊢
    have hset : ({P : Fin n → ℝ | ∀ j, P j = 0 ∨ P j = 1} ∩ (LinearMap.range g : Set (Fin n → ℝ)))
        = ((Finset.univ.image (fun b : Fin k → Bool => g (fun i => if b i then (1:ℝ) else 0)) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · rintro ⟨hxZ, a, rfl⟩
        have h01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
          have := hxZ (Fin.castLE hk i)
          rw [hg, dif_pos (by simp)] at this
          exact this
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨fun i => decide (a i = 1), Finset.mem_univ _, ?_⟩
        congr 1
        funext i
        rcases h01 i with h | h <;> simp [h]
      · intro hx
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        refine ⟨?_, LinearMap.mem_range_self _ _⟩
        intro j
        rw [hg]
        split_ifs <;> simp
    refine ⟨LinearMap.range g, hrank, ?_⟩
    show _ = 2 ^ k
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  · rintro y ⟨V, hV, rfl⟩
    have hfin : Module.finrank ℝ V = k := by
      have := Module.finrank_eq_rank ℝ V
      rw [hV] at this
      exact_mod_cast this
    obtain ⟨S, hS, hinj⟩ := aux k V hfin.le
    show _ ≤ 2 ^ k
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun x => fun j : S => decide (x j = 1))
      (fun _ _ => Set.mem_univ _) ?_ Set.finite_univ) ?_
    · intro x hx y hy hxy
      have hx1 : ∀ j, x j = 0 ∨ x j = 1 := hx.1
      have hy1 : ∀ j, y j = 0 ∨ y j = 1 := hy.1
      have key : ∀ j ∈ S, x j = y j := by
        intro j hj
        have h1 := congrFun hxy ⟨j, hj⟩
        simp only at h1
        rcases hx1 j with h2 | h2 <;> rcases hy1 j with h3 | h3 <;> simp [h2, h3] at h1 ⊢
      have h0 : x - y = 0 := hinj (x - y) (V.sub_mem hx.2 hy.2)
        (fun j hj => by rw [Pi.sub_apply, key j hj, sub_self])
      exact sub_eq_zero.mp h0
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_coe]
      exact Nat.pow_le_pow_right (by norm_num) hS
