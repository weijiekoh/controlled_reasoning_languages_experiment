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
  -- key: some k coordinates determine every vector of a subspace of dimension ≤ k
  have key : ∀ m : ℕ, ∀ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V ≤ m →
      ∃ I : Finset (Fin n), I.card ≤ m ∧ ∀ u ∈ V, (∀ i ∈ I, u i = 0) → u = 0 := by
    intro m
    induction m with
    | zero =>
      intro V hV
      refine ⟨∅, by simp, ?_⟩
      intro u hu _
      have hbot : V = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      subst hbot
      simpa using hu
    | succ m ih =>
      intro V hV
      by_cases h : ∀ u ∈ V, ∀ i, u i = 0
      · refine ⟨∅, by simp, ?_⟩
        intro u hu _
        funext i
        exact h u hu i
      · push_neg at h
        obtain ⟨u, hu, i, hi⟩ := h
        set W : Submodule ℝ (Fin n → ℝ) := V ⊓ LinearMap.ker (LinearMap.proj i) with hWdef
        have hWV : W < V := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro heq
          have hmem : u ∈ W := heq ▸ hu
          exact hi (hmem.2 : u i = 0)
        have hfin := Submodule.finrank_lt_finrank_of_lt hWV
        obtain ⟨I, hI, hIW⟩ := ih W (by omega)
        refine ⟨insert i I, ?_, ?_⟩
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · intro w hw hzero
          apply hIW w ⟨hw, (hzero i (Finset.mem_insert_self _ _) : w i = 0)⟩
          intro j hj
          exact hzero j (Finset.mem_insert_of_mem hj)
  -- the linear map R^k → R^n padding with zeros
  obtain ⟨L, hL⟩ : ∃ L : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      ∀ c j, L c j = if h : (j : ℕ) < k then c ⟨j, h⟩ else 0 :=
    ⟨{ toFun := fun c j => if h : (j : ℕ) < k then c ⟨j, h⟩ else 0
       map_add' := by
         intro c d
         funext j
         by_cases h : (j : ℕ) < k <;> simp [h]
       map_smul' := by
         intro a c
         funext j
         by_cases h : (j : ℕ) < k <;> simp [h] }, fun c j => rfl⟩
  have hLc : ∀ c (i : Fin k), L c (Fin.castLE hk i) = c i := by
    intro c i
    rw [hL]
    simp
  have hinj : Function.Injective L := by
    intro c d h
    funext i
    have := congrFun h (Fin.castLE hk i)
    rw [hLc, hLc] at this
    exact this
  have hrank : Module.rank ℝ (LinearMap.range L) = k := by
    have := (LinearEquiv.ofInjective L hinj).rank_eq
    rw [rank_fin_fun] at this
    exact this.symm
  have hginj : Function.Injective
      (fun β : Fin k → Bool => L (fun i => if β i then (1:ℝ) else 0)) := by
    intro β γ h
    have h' := hinj h
    funext i
    have := congrFun h' i
    revert this
    cases β i <;> cases γ i <;> norm_num
  have hset : {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (LinearMap.range L : Set (Fin n → ℝ))
      = (fun β : Fin k → Bool => L (fun i => if β i then (1:ℝ) else 0)) '' Set.univ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_range,
      Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨hx, c, rfl⟩
      refine ⟨fun i => decide (c i = 1), ?_⟩
      congr 1
      funext i
      have := hx (Fin.castLE hk i)
      rw [hLc] at this
      rcases this with h | h <;> simp [h]
    · rintro ⟨β, rfl⟩
      refine ⟨?_, ⟨_, rfl⟩⟩
      intro j
      rw [hL]
      by_cases h : (j : ℕ) < k
      · rw [dif_pos h]
        rcases Bool.eq_false_or_eq_true (β ⟨j, h⟩) with e | e <;> simp [e]
      · rw [dif_neg h]
        exact Or.inl rfl
  constructor
  · refine ⟨LinearMap.range L, hrank, ?_⟩
    show Set.ncard _ = 2 ^ k
    rw [hset, Set.ncard_image_of_injective _ hginj, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp
  · rintro y ⟨V, hV, rfl⟩
    show Set.ncard _ ≤ 2 ^ k
    have hfin : Module.finrank ℝ V = k := by
      have := Module.finrank_eq_rank ℝ V
      rw [hV] at this
      exact_mod_cast this
    obtain ⟨I, hIcard, hIinj⟩ := key k V hfin.le
    have hle := Set.ncard_le_ncard_of_injOn
      (s := {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ)))
      (fun x : Fin n → ℝ => (fun i : I => decide (x i = 1))) (t := Set.univ)
      (fun _ _ => Set.mem_univ _) ?_ Set.finite_univ
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
      have hc : Fintype.card (↥I → Bool) = 2 ^ I.card := by simp
      rw [hc] at hle
      exact hle.trans (Nat.pow_le_pow_right (by norm_num) hIcard)
    · rintro x ⟨hx, hxV⟩ y ⟨hy, hyV⟩ hxy
      have hx1 : ∀ j, x j = 0 ∨ x j = 1 := hx
      have hy1 : ∀ j, y j = 0 ∨ y j = 1 := hy
      have hagree : ∀ i ∈ I, x i = y i := by
        intro i hi
        have h1 := congrFun hxy ⟨i, hi⟩
        simp only [decide_eq_decide] at h1
        rcases hx1 i with a | a <;> rcases hy1 i with b | b <;> simp [a, b] at h1 ⊢
      have hu : x - y ∈ V := V.sub_mem hxV hyV
      have := hIinj (x - y) hu (fun i hi => by simp [hagree i hi])
      exact sub_eq_zero.mp this
