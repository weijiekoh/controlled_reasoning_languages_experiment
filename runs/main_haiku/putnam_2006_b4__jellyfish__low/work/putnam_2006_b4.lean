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
      (putnam_2006_b4_solution k) := by
  classical
  subst hZ
  have key : ∀ (V : Subspace ℝ (Fin n → ℝ)), Module.rank ℝ V = k →
      ∃ S : Finset (Fin n), S.card ≤ k ∧ ∀ x ∈ V, (∀ j ∈ S, x j = 0) → x = 0 := by
    intro V hV
    have hfin : Module.Finite ℝ V := Module.finite_of_rank_eq_nat (by rw [hV])
    have hfd : Module.finrank ℝ V = k := by
      have := Module.finrank_eq_rank ℝ V
      rw [hV] at this
      exact_mod_cast this
    let P : Finset (Fin n) → Prop := fun S => ∀ x ∈ V, (∀ j ∈ S, x j = 0) → x = 0
    have hP : ∃ S, P S := ⟨Finset.univ, fun x _ h => funext fun j => h j (Finset.mem_univ j)⟩
    obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
      ((Finset.univ : Finset (Finset (Fin n))).filter P) Finset.card
      (by obtain ⟨S, hS⟩ := hP; exact ⟨S, by simp [hS]⟩)
    have hSP : P S := (Finset.mem_filter.mp hS).2
    refine ⟨S, ?_, hSP⟩
    have hwit : ∀ j : Fin n, ∃ x : V, j ∈ S → ((∀ i ∈ S, i ≠ j → (x : Fin n → ℝ) i = 0) ∧ (x : Fin n → ℝ) j ≠ 0) := by
      intro j
      by_cases hj : j ∈ S
      · have hnot : ¬ P (S.erase j) := by
          intro hP'
          have h1 := hmin (S.erase j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
          have h2 := Finset.card_erase_lt_of_mem hj
          omega
        unfold P at hnot
        push Not at hnot
        obtain ⟨x, hxV, hx0, hxne⟩ := hnot
        refine ⟨⟨x, hxV⟩, fun _ => ⟨fun i hi hij => hx0 i (Finset.mem_erase.mpr ⟨hij, hi⟩), ?_⟩⟩
        intro hxj
        apply hxne
        apply hSP x hxV
        intro i hi
        by_cases hij : i = j
        · subst hij; exact hxj
        · exact hx0 i (Finset.mem_erase.mpr ⟨hij, hi⟩)
      · exact ⟨0, fun h => absurd h hj⟩
    choose w hw using hwit
    have hli : LinearIndependent ℝ (fun j : S => w j) := by
      rw [linearIndependent_iff']
      intro s g hsum i hi
      have hcoord := congrArg (fun y : V => (y : Fin n → ℝ) i.1) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
      rw [Finset.sum_eq_single i] at hcoord
      · obtain ⟨h1, h2⟩ := hw i.1 i.2
        rcases mul_eq_zero.mp hcoord with h | h
        · exact h
        · exact absurd h h2
      · intro t _ hti
        obtain ⟨h1, _⟩ := hw t.1 t.2
        have : (w t.1 : Fin n → ℝ) i.1 = 0 := h1 i.1 i.2 (fun e => hti (Subtype.ext e).symm)
        simp [this]
      · intro hi'; exact absurd hi hi'
    have := hli.fintype_card_le_finrank
    rw [hfd] at this
    simpa using this
  constructor
  · let L : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun x j => if h : j.val < k then x ⟨j.val, h⟩ else 0
        map_add' := by intro x y; funext j; by_cases h : j.val < k <;> simp [h]
        map_smul' := by intro c x; funext j; by_cases h : j.val < k <;> simp [h] }
    have hLx : ∀ x j, (L x) j = if h : j.val < k then x ⟨j.val, h⟩ else 0 := fun x j => rfl
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      funext i
      have := congrFun hx ⟨i.val, by omega⟩
      rw [hLx, dif_pos i.isLt] at this
      simpa using this
    refine ⟨LinearMap.range L, ?_, ?_⟩
    · rw [rank_range_of_injective L hinj, rank_fin_fun]
    · have hset : {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (LinearMap.range L : Set (Fin n → ℝ))
          = (fun b : Fin k → Bool => L (fun i => if b i then (1:ℝ) else 0)) '' Set.univ := by
        ext P
        constructor
        · rintro ⟨hPZ, x, rfl⟩
          refine ⟨fun i => decide (x i = 1), Set.mem_univ _, ?_⟩
          have hPZ' : ∀ j, L x j = 0 ∨ L x j = 1 := hPZ
          apply congrArg L
          funext i
          have h := hPZ' ⟨i.val, by omega⟩
          rw [hLx, dif_pos i.isLt] at h
          rcases h with h | h <;> simp [h]
        · rintro ⟨b, -, rfl⟩
          refine ⟨?_, LinearMap.mem_range.mpr ⟨_, rfl⟩⟩
          simp only [Set.mem_setOf_eq]
          intro j
          rw [hLx]
          by_cases h : j.val < k
          · rw [dif_pos h]
            cases hb : b ⟨j.val, h⟩ <;> simp
          · rw [dif_neg h]; simp
      have hinj2 : Function.Injective (fun b : Fin k → Bool => L (fun i => if b i then (1:ℝ) else 0)) := by
        intro b c h
        have h' := hinj h
        funext i
        have := congrFun h' i
        cases hb : b i <;> cases hc : c i <;> simp_all
      rw [hset, Set.ncard_image_of_injective _ hinj2, Set.ncard_univ, Nat.card_eq_fintype_card]
      simp
  · rintro y ⟨V, hV, rfl⟩
    obtain ⟨S, hcard, hS⟩ := key V hV
    have hbound : ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ))).ncard
        ≤ (Set.univ : Set (S → Bool)).ncard := by
      apply Set.ncard_le_ncard_of_injOn (fun P : Fin n → ℝ => fun i : S => decide (P i = 1))
      · intro P _; exact Set.mem_univ _
      · rintro P ⟨hPZ, hPV⟩ Q ⟨hQZ, hQV⟩ hPQ
        have hzero : P - Q = 0 := by
          apply hS (P - Q) (V.sub_mem hPV hQV)
          intro j hj
          have h := congrFun hPQ ⟨j, hj⟩
          simp only [decide_eq_decide] at h
          have hPZ' : P j = 0 ∨ P j = 1 := hPZ j
          have hQZ' : Q j = 0 ∨ Q j = 1 := hQZ j
          rcases hPZ' with h1 | h1 <;> rcases hQZ' with h2 | h2 <;>
            simp_all
        exact sub_eq_zero.mp hzero
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe] at hbound
    exact le_trans hbound (Nat.pow_le_pow_right (by norm_num) hcard)
