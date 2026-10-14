import Mathlib

open Filter Topology

/--
Say that an $n$-by-$n$ matrix $A=(a_{ij})_{1 \leq i,j \leq n}$ with integer entries is \emph{very odd} if, for every nonempty subset $S$ of $\{1,2,\dots,n\}$, the $|S|$-by-$|S|$ submatrix $(a_{ij})_{i,j \in S}$ has odd determinant. Prove that if $A$ is very odd, then $A^k$ is very odd for every $k \geq 1$.
-/
theorem putnam_2021_b5
(n : ℕ)
(npos : n ≥ 1)
(veryodd : Matrix (Fin n) (Fin n) ℤ → Prop)
(hveryodd : ∀ A, veryodd A ↔ ∀ m ∈ Set.Icc 1 n, ∀ reind : Fin m → Fin n, Function.Injective reind → Odd (A.submatrix reind reind).det)
: ∀ A, veryodd A → (∀ k ≥ 1, veryodd (A ^ k)) :=
by
  intro A hA k hk
  rw [hveryodd] at hA ⊢
  have H : ∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ r : Fin m → Fin n, Function.Injective r →
      Odd (A.submatrix r r).det := fun m h1 h2 r hr => hA m ⟨h1, h2⟩ r hr
  classical
  obtain ⟨E, hEdef⟩ : ∃ E : Fin n → Fin n → Prop, ∀ i j, E i j ↔ (i ≠ j ∧ Odd (A i j)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hcastodd : ∀ z : ℤ, Odd z ↔ ((z : ZMod 2) = 1) := fun z => ZMod.intCast_eq_one_iff_odd.symm
  have hZ : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hdiag : ∀ i, Odd (A i i) := by
    intro i
    have := H 1 le_rfl (by omega) (fun _ => i) (fun a b _ => Subsingleton.elim a b)
    simpa [Matrix.det_fin_one] using this
  have modlem : ∀ x k : ℕ, 0 < k → (x % k + 1 < k ∧ (x + 1) % k = x % k + 1) ∨
      (x % k + 1 = k ∧ (x + 1) % k = 0) := by
    intro x k hk
    have h1 := Nat.mod_lt x hk
    rcases Nat.lt_or_ge (x % k + 1) k with h | h
    · left
      refine ⟨h, ?_⟩
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt h]
    · right
      have h2 : x % k + 1 = k := by omega
      refine ⟨h2, ?_⟩
      have hx := Nat.div_add_mod x k
      have e : x + 1 = k * (x / k + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; linarith
      rw [e, Nat.mul_mod_right]
  have Glem : ∀ c : ℕ → Fin n, (∀ x, E (c x) (c (x + 1))) → ∀ s m : ℕ, 0 < m →
      E (c (s + m - 1)) (c s) → ∃ c' : ℕ → Fin n, (∀ x, E (c' x) (c' (x + 1))) ∧
        ∀ x, c' (x + m) = c' x := by
    intro c hc s m hm hcl
    refine ⟨fun x => c (s + x % m), ?_, ?_⟩
    · intro x
      show E (c (s + x % m)) (c (s + (x + 1) % m))
      rcases modlem x m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        have := hc (s + x % m)
        rw [← Nat.add_assoc]; exact this
      · rw [h2]
        have e : s + x % m = s + m - 1 := by omega
        rw [e, Nat.add_zero]; exact hcl
    · intro x
      show c (s + (x + m) % m) = c (s + x % m)
      rw [Nat.add_mod_right]
  have Tlem : ∀ x y : Fin n, Relation.TransGen E x y → ∃ k, 0 < k ∧ ∃ f : ℕ → Fin n,
      f 0 = x ∧ f k = y ∧ ∀ j < k, E (f j) (f (j + 1)) := by
    intro x y h
    induction h with
    | @single w h =>
      refine ⟨1, one_pos, fun j => if j = 0 then x else w, by simp, by simp, ?_⟩
      intro j hj
      have : j = 0 := by omega
      subst this
      simpa using h
    | @tail b z _ hbz ih =>
      obtain ⟨k, hk, f, h0, hkf, hf⟩ := ih
      refine ⟨k + 1, by omega, fun j => if j ≤ k then f j else z, by simp [h0], by simp, ?_⟩
      intro j hj
      by_cases hjk : j < k
      · show E (if j ≤ k then f j else z) (if j + 1 ≤ k then f (j + 1) else z)
        rw [if_pos (by omega), if_pos (by omega)]
        exact hf j hjk
      · have hjk' : j = k := by omega
        show E (if j ≤ k then f j else z) (if j + 1 ≤ k then f (j + 1) else z)
        rw [if_pos (by omega), if_neg (by omega), hjk', hkf]
        exact hbz
  have CL : ∀ L : ℕ, ∀ c : ℕ → Fin n, 0 < L → (∀ x, c (x + L) = c x) →
      (∀ x, E (c x) (c (x + 1))) → False := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ih =>
    intro c hL hper hc
    have inj0 : ∀ s t, s < t → t < L → c s = c t → False := by
      intro s t hst htL hct
      have e := hc (s + (t - s) - 1)
      have e2 : s + (t - s) - 1 + 1 = t := by omega
      rw [e2, ← hct] at e
      obtain ⟨c', hc', hper'⟩ := Glem c hc s (t - s) (by omega) e
      exact ih (t - s) (by omega) c' (by omega) hper' hc'
    have inj : ∀ s t, s < L → t < L → c s = c t → s = t := by
      intro s t hs ht hst
      rcases lt_trichotomy s t with h | h | h
      · exact (inj0 s t h ht hst).elim
      · exact h
      · exact (inj0 t s h hs hst.symm).elim
    have chord : ∀ t u, t < L → u < L → E (c t) (c u) →
        u = t + 1 ∨ (t + 1 = L ∧ u = 0) := by
      intro t u ht hu hE'
      by_contra hcon
      have hne1 : u ≠ t + 1 := fun h => hcon (Or.inl h)
      have hne0 : ¬ (t + 1 = L ∧ u = 0) := fun h => hcon (Or.inr h)
      have hut : u ≠ t := fun h => ((hEdef _ _).mp hE').1 (by rw [h])
      rcases Nat.lt_or_gt_of_ne hut with hlt | hgt
      · obtain ⟨c', hc', hper'⟩ := Glem c hc u (t - u + 1) (by omega) (by
          have e : u + (t - u + 1) - 1 = t := by omega
          rw [e]; exact hE')
        exact ih (t - u + 1) (by omega) c' (by omega) hper' hc'
      · obtain ⟨c', hc', hper'⟩ := Glem c hc u (t + L - u + 1) (by omega) (by
          have e : u + (t + L - u + 1) - 1 = t + L := by omega
          rw [e, hper t]; exact hE')
        exact ih (t + L - u + 1) (by omega) c' (by omega) hper' hc'
    have hL2 : 2 ≤ L := by
      by_contra hcon
      have hL1 : L = 1 := by omega
      have e := hc 0
      have e2 := hper 0
      rw [hL1] at e2
      rw [e2] at e
      exact ((hEdef _ _).mp e).1 rfl
    have row : ∀ t : Fin L, ∑ u : Fin L, ((A (c t.val) (c u.val) : ℤ) : ZMod 2) = 0 := by
      intro t
      obtain ⟨t', ht'⟩ : ∃ t' : Fin L, t'.val = (t.val + 1) % L :=
        ⟨⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩, rfl⟩
      have hval : (t'.val = t.val + 1 ∧ t.val + 1 < L) ∨ (t'.val = 0 ∧ t.val + 1 = L) := by
        have := modlem t.val L hL
        rw [Nat.mod_eq_of_lt t.isLt] at this
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨by rw [ht', h2], h1⟩
        · right; exact ⟨by rw [ht', h2], h1⟩
      have hne : t'.val ≠ t.val := by omega
      have hne' : t' ≠ t := fun h => hne (by rw [h])
      have hc' : c t'.val = c (t.val + 1) := by
        rcases hval with ⟨h1, _⟩ | ⟨h1, h2⟩
        · rw [h1]
        · rw [h1, h2]; simpa using (hper 0).symm
      have hEt : E (c t.val) (c t'.val) := by rw [hc']; exact hc t.val
      have hinjne : ∀ u : Fin L, u ≠ t → c u.val ≠ c t.val :=
        fun u hu h => hu (Fin.ext (inj _ _ u.isLt t.isLt h))
      have hterm : ∀ u : Fin L, u ≠ t → u ≠ t' →
          ((A (c t.val) (c u.val) : ℤ) : ZMod 2) = 0 := by
        intro u hu hu'
        by_contra hz
        have hodd : Odd (A (c t.val) (c u.val)) := by
          rw [hcastodd]; exact hZ _ hz
        have hE2 : E (c t.val) (c u.val) := (hEdef _ _).mpr ⟨fun h => hinjne u hu h.symm, hodd⟩
        rcases chord t.val u.val t.isLt u.isLt hE2 with h | h <;>
          exact hu' (Fin.ext (by omega))
      have h1 : ((A (c t.val) (c t.val) : ℤ) : ZMod 2) = 1 := (hcastodd _).mp (hdiag _)
      have h2 : ((A (c t.val) (c t'.val) : ℤ) : ZMod 2) = 1 :=
        (hcastodd _).mp ((hEdef _ _).mp hEt).2
      rw [Finset.sum_eq_add (f := fun u : Fin L => ((A (c t.val) (c u.val) : ℤ) : ZMod 2))
        t t' (fun h => hne' h.symm) (fun u _ hu => hterm u hu.1 hu.2)
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp only [h1, h2]
      decide
    obtain ⟨r, hr⟩ : ∃ r : Fin L → Fin n, ∀ u, r u = c u.val := ⟨_, fun _ => rfl⟩
    have hrinj : Function.Injective r := by
      intro a b h
      rw [hr, hr] at h
      exact Fin.ext (inj _ _ a.isLt b.isLt h)
    have hLn : L ≤ n := by
      have := Fintype.card_le_of_injective r hrinj
      simpa using this
    have hd := H L hL hLn r hrinj
    have hdz : (((A.submatrix r r).det : ℤ) : ZMod 2) = 0 := by
      have hmap := RingHom.map_det (Int.castRingHom (ZMod 2)) (A.submatrix r r)
      rw [show (((A.submatrix r r).det : ℤ) : ZMod 2) = (Int.castRingHom (ZMod 2)) (A.submatrix r r).det from rfl, hmap]
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun _ => 1, fun h => ?_, ?_⟩
      · have := congrFun h ⟨0, hL⟩
        simp at this
      · funext t
        simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, RingHom.mapMatrix_apply,
          Matrix.map_apply, Matrix.submatrix_apply, Int.coe_castRingHom, hr]
        exact row t
    have h1 := (hcastodd _).mp hd
    rw [hdz] at h1
    exact absurd h1 (by decide)
  have acyc : ∀ i, ¬ Relation.TransGen E i i := by
    intro i h
    obtain ⟨k, hk, f, h0, hkf, hf⟩ := Tlem i i h
    refine CL k (fun x => f (x % k)) hk ?_ ?_
    · intro x
      show f ((x + k) % k) = f (x % k)
      rw [Nat.add_mod_right]
    · intro x
      show E (f (x % k)) (f ((x + 1) % k))
      rcases modlem x k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; exact hf (x % k) (by omega)
      · rw [h2, h0]
        have := hf (x % k) (by omega)
        rw [h1, hkf] at this
        exact this
  obtain ⟨b, hb⟩ : ∃ b : Fin n → ℕ, ∀ i,
      b i = (Finset.univ.filter (fun j => Relation.TransGen E j i)).card := ⟨_, fun _ => rfl⟩
  have hbE : ∀ i j, E i j → b i < b j := by
    intro i j hij
    rw [hb, hb]
    have hsub : Finset.univ.filter (fun x => Relation.TransGen E x i) ⊆
        Finset.univ.filter (fun x => Relation.TransGen E x j) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, Relation.TransGen.tail hx.2 hij⟩
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Relation.TransGen.single hij⟩
    · rw [Finset.mem_filter]; intro h; exact acyc i h.2
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin n) (Fin n) (ZMod 2),
      B = (Int.castRingHom (ZMod 2)).mapMatrix A := ⟨_, rfl⟩
  have hBent : ∀ i j, B i j = ((A i j : ℤ) : ZMod 2) := by
    intro i j; rw [hBdef]; rfl
  have hPB : ∀ i j, B i j ≠ 0 → i = j ∨ b i < b j := by
    intro i j hne
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      apply hbE
      rw [hEdef]
      refine ⟨hij, ?_⟩
      rw [hBent] at hne
      exact (hcastodd _).mpr (hZ _ hne)
  have hdB : ∀ i, B i i = 1 := by
    intro i; rw [hBent]; exact (hcastodd _).mp (hdiag i)
  have hmul : ∀ M N : Matrix (Fin n) (Fin n) (ZMod 2),
      (∀ i j, M i j ≠ 0 → i = j ∨ b i < b j) → (∀ i, M i i = 1) →
      (∀ i j, N i j ≠ 0 → i = j ∨ b i < b j) → (∀ i, N i i = 1) →
      (∀ i j, (M * N) i j ≠ 0 → i = j ∨ b i < b j) ∧ (∀ i, (M * N) i i = 1) := by
    intro M N hM hMd hN hNd
    have term2 : ∀ i j l, M i l * N l j ≠ 0 → (i = l ∨ b i < b l) ∧ (l = j ∨ b l < b j) :=
      fun i j l h => ⟨hM i l (left_ne_zero_of_mul h), hN l j (right_ne_zero_of_mul h)⟩
    constructor
    · intro i j h
      by_contra hc
      apply h
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_contra hl
      obtain ⟨h1, h2⟩ := term2 i j l hl
      apply hc
      rcases h1 with e | e <;> rcases h2 with e' | e'
      · exact Or.inl (e.trans e')
      · exact Or.inr (by rw [e]; exact e')
      · exact Or.inr (by rw [← e']; exact e)
      · exact Or.inr (lt_trans e e')
    · intro i
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [hMd i, hNd i, one_mul]
      · intro l _ hl
        by_contra hz
        obtain ⟨h1, h2⟩ := term2 i i l hz
        rcases h1 with e | e <;> rcases h2 with e' | e'
        · exact hl e.symm
        · exact hl e.symm
        · exact hl e'
        · exact lt_asymm e e'
      · intro h; exact absurd (Finset.mem_univ i) h
  have hP : ∀ k, (∀ i j, (B ^ (k + 1)) i j ≠ 0 → i = j ∨ b i < b j) ∧
      (∀ i, (B ^ (k + 1)) i i = 1) := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one]; exact ⟨hPB, hdB⟩
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih.1 ih.2 hPB hdB
  intro m _ reind hr
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hC : B ^ (k' + 1) = (Int.castRingHom (ZMod 2)).mapMatrix (A ^ (k' + 1)) := by
    rw [hBdef, map_pow]
  have hPk := hP k'
  have hdetC : ((B ^ (k' + 1)).submatrix reind reind).det = 1 := by
    set σ := Tuple.sort (fun i => b (reind i)) with hσ
    rw [← Matrix.det_submatrix_equiv_self σ]
    have hUT : (((B ^ (k' + 1)).submatrix reind reind).submatrix σ σ).IsUpperTriangular := by
      intro i j hji
      show (B ^ (k' + 1)) (reind (σ i)) (reind (σ j)) = 0
      by_contra hne
      rcases hPk.1 (reind (σ i)) (reind (σ j)) hne with e | e
      · exact absurd (σ.injective (hr e)) (ne_of_gt hji)
      · have hmono : b (reind (σ j)) ≤ b (reind (σ i)) :=
          Tuple.monotone_sort (fun i => b (reind i)) (le_of_lt hji)
        exact absurd e (not_lt.mpr hmono)
    rw [Matrix.det_of_isUpperTriangular hUT]
    exact Finset.prod_eq_one (fun i _ => hPk.2 (reind (σ i)))
  have hcast : (((A ^ (k' + 1)).submatrix reind reind).det : ZMod 2) = 1 := by
    have hmap := RingHom.map_det (Int.castRingHom (ZMod 2)) ((A ^ (k' + 1)).submatrix reind reind)
    have hsub : (Int.castRingHom (ZMod 2)).mapMatrix ((A ^ (k' + 1)).submatrix reind reind) =
        (B ^ (k' + 1)).submatrix reind reind := by
      rw [hC]; ext i j; simp
    rw [show (((A ^ (k' + 1)).submatrix reind reind).det : ZMod 2) =
      (Int.castRingHom (ZMod 2)) ((A ^ (k' + 1)).submatrix reind reind).det from rfl, hmap, hsub, hdetC]
  exact (hcastodd _).mpr hcast
