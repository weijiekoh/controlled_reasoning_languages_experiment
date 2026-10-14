import Mathlib
open Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diag_one (B : Matrix ι ι (ZMod 2))
  (H : ∀ S : Finset ι, S.Nonempty → det (B.submatrix (fun x : S => x.1) (fun x : S => x.1)) = 1) :
  ∀ x, B x x = 1 := by
  intro x
  have := H {x} ⟨x, by simp⟩
  rw [Matrix.det_unique] at this
  simpa using this

lemma sink_lem (B : Matrix ι ι (ZMod 2))
  (H : ∀ S : Finset ι, S.Nonempty → det (B.submatrix (fun x : S => x.1) (fun x : S => x.1)) = 1) :
  ∀ S : Finset ι, S.Nonempty → ∃ i ∈ S, ∀ j ∈ S, j ≠ i → B i j = 0 := by
  classical
  intro S hS
  by_contra hcon
  push_neg at hcon
  let Pr : Finset ι → Prop := fun T => T.Nonempty ∧ ∀ i ∈ T, ∃ j ∈ T, j ≠ i ∧ B i j ≠ 0
  have hPS : Pr S := ⟨hS, fun i hi => by
    obtain ⟨j, hj, h1, h2⟩ := hcon i hi
    exact ⟨j, hj, h1, h2⟩⟩
  obtain ⟨T, hT, hmin⟩ := (measure Finset.card).wf.has_min {T | Pr T} ⟨S, hPS⟩
  have hmin' : ∀ T', Pr T' → T' ⊆ T → T' = T := by
    intro T' hT' hsub
    by_contra hne
    exact hmin T' hT' (Finset.card_lt_card (lt_of_le_of_ne hsub hne))
  obtain ⟨hTne, hTp⟩ := hT
  have hsurj : ∀ g : ι → ι, (∀ i ∈ T, g i ∈ T ∧ g i ≠ i ∧ B i (g i) ≠ 0) →
      T.image g = T := by
    intro g hg
    apply hmin'
    · refine ⟨hTne.image g, ?_⟩
      intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨g (g x), Finset.mem_image.mpr ⟨g x, (hg x hx).1, rfl⟩, (hg _ (hg x hx).1).2.1,
        (hg _ (hg x hx).1).2.2⟩
    · intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      exact (hg x hx).1
  have hinj : ∀ g : ι → ι, (∀ i ∈ T, g i ∈ T ∧ g i ≠ i ∧ B i (g i) ≠ 0) →
      Set.InjOn g T := by
    intro g hg
    rw [← Finset.card_image_iff, hsurj g hg]
  have h1 : ∀ i ∈ T, ∃ j, j ∈ T ∧ j ≠ i ∧ B i j ≠ 0 := fun i hi => by
    obtain ⟨j, hj, h1, h2⟩ := hTp i hi
    exact ⟨j, hj, h1, h2⟩
  choose! g hg using h1
  have hg' : ∀ i ∈ T, g i ∈ T ∧ g i ≠ i ∧ B i (g i) ≠ 0 := fun i hi => ⟨(hg i hi).1, (hg i hi).2.1, (hg i hi).2.2⟩
  have huniq : ∀ i ∈ T, ∀ j ∈ T, j ≠ i → B i j ≠ 0 → j = g i := by
    intro i hi j hj hji hB
    by_contra hne
    have hg2 : ∀ x ∈ T, (Function.update g i j) x ∈ T ∧ (Function.update g i j) x ≠ x ∧
        B x ((Function.update g i j) x) ≠ 0 := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; simpa using ⟨hj, hji, hB⟩
      · simpa [Function.update_of_ne hxi] using hg' x hx
    have hy : g i ∈ T.image (Function.update g i j) := by rw [hsurj _ hg2]; exact (hg' i hi).1
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hy
    by_cases hxi : x = i
    · subst hxi; simp at hxe; exact hne hxe
    · rw [Function.update_of_ne hxi] at hxe
      exact hxi (hinj g hg' hx hi hxe)
  have hd := H T hTne
  have h0 : det (B.submatrix (fun x : T => x.1) (fun x : T => x.1)) = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hTne
      intro h
      have := congrFun h ⟨x, hx⟩
      simp at this
    · ext x
      simp only [Matrix.mulVec, dotProduct, mul_one, Matrix.submatrix_apply, Pi.zero_apply]
      rw [Finset.sum_coe_sort T (fun k => B x.1 k)]
      rw [← Finset.sum_subset (s₁ := {x.1, g x.1}) (by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact x.2
        · rw [Finset.mem_singleton.mp hk]; exact (hg' _ x.2).1)]
      · rw [Finset.sum_pair (Ne.symm (hg' _ x.2).2.1)]
        have := (hg' _ x.2).2.2
        have h2 : B x.1 (g x.1) = 1 := by
          generalize B x.1 (g x.1) = z at this ⊢
          revert z; decide
        rw [h2, diag_one B H]; decide
      · intro k hk hkn
        by_contra hne
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkn
        exact hkn.2 (huniq x.1 x.2 k hk hkn.1 hne)
  rw [h0] at hd
  exact zero_ne_one hd

lemma rank_lem (B : Matrix ι ι (ZMod 2))
  (hs : ∀ S : Finset ι, S.Nonempty → ∃ i ∈ S, ∀ j ∈ S, j ≠ i → B i j = 0) :
  ∀ n, ∀ S : Finset ι, S.card = n → ∃ r : ι → ℕ, Set.InjOn r S ∧
    ∀ i ∈ S, ∀ j ∈ S, j ≠ i → B i j ≠ 0 → r j < r i := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨i, hi, hsk⟩ := hs S hne
    obtain ⟨r', hinj, hedge⟩ := ih (S.erase i) (by rw [Finset.card_erase_of_mem hi]; omega)
    refine ⟨fun x => if x = i then 0 else r' x + 1, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only at hxy
      by_cases hxi : x = i <;> by_cases hyi : y = i
      · rw [hxi, hyi]
      · simp [hxi, hyi] at hxy
      · simp [hxi, hyi] at hxy
      · simp [hxi, hyi] at hxy
        exact hinj (Finset.mem_erase.mpr ⟨hxi, hx⟩) (Finset.mem_erase.mpr ⟨hyi, hy⟩) hxy
    · intro a ha b hb hba hB
      have hai : a ≠ i := by
        rintro rfl
        exact hB (hsk b hb hba)
      by_cases hbi : b = i
      · simp [hai, hbi]
      · simp only [hai, hbi, if_false]
        have := hedge a (Finset.mem_erase.mpr ⟨hai, ha⟩) b (Finset.mem_erase.mpr ⟨hbi, hb⟩) hba hB
        omega

def Tri (r : ι → ℕ) (M : Matrix ι ι (ZMod 2)) : Prop :=
  (∀ i, M i i = 1) ∧ ∀ i j, i ≠ j → M i j ≠ 0 → r j < r i

lemma Tri.mul {r : ι → ℕ} {M M' : Matrix ι ι (ZMod 2)} (h : Tri r M) (h' : Tri r M') :
    Tri r (M * M') := by
  refine ⟨fun i => ?_, fun i j hij hne => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [h.1, h'.1]; rfl
    · intro l _ hl
      by_contra hne
      rcases mul_ne_zero_iff.mp hne with ⟨a, b⟩
      have := h.2 i l (Ne.symm hl) a
      have := h'.2 l i hl b
      omega
    · simp
  · rw [Matrix.mul_apply] at hne
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rcases mul_ne_zero_iff.mp hl with ⟨a, b⟩
    by_cases hli : l = i
    · subst hli; exact h'.2 _ _ hij b
    · by_cases hlj : l = j
      · subst hlj; exact h.2 _ _ hij a
      · have := h.2 i l (Ne.symm hli) a
        have := h'.2 l j hlj b
        omega

lemma Tri.pow {r : ι → ℕ} {M : Matrix ι ι (ZMod 2)} (h : Tri r M) (k : ℕ) : Tri r (M ^ k) := by
  induction k with
  | zero => exact ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply, hij]⟩
  | succ k ih => rw [pow_succ]; exact ih.mul h

lemma Tri.det {r : ι → ℕ} (hr : Function.Injective r) {M : Matrix ι ι (ZMod 2)} (h : Tri r M)
    {m : ℕ} (reind : Fin m → ι) (hre : Function.Injective reind) :
    det (M.submatrix reind reind) = 1 := by
  classical
  let b : Fin m → ℤ := fun a => -((r (reind a) : ℕ) : ℤ)
  have hb : (M.submatrix reind reind).BlockTriangular b := by
    intro a c hac
    by_contra hne
    have hne' : M (reind a) (reind c) ≠ 0 := hne
    by_cases hh : reind a = reind c
    · simp only [b, hh] at hac; omega
    · have := h.2 _ _ hh hne'
      simp only [b] at hac; omega
  have binj : Function.Injective b := by
    intro a c hac
    apply hre; apply hr
    simp only [b] at hac; omega
  rw [Matrix.BlockTriangular.det hb]
  apply Finset.prod_eq_one
  intro k hk
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
  haveI : Unique {x // b x = b a} := { default := ⟨a, rfl⟩, uniq := fun x => Subtype.ext (binj x.2) }
  rw [Matrix.det_unique]
  have : (default : {x // b x = b a}).1 = a := binj (default : {x // b x = b a}).2
  show M (reind (default : {x // b x = b a}).1) (reind (default : {x // b x = b a}).1) = 1
  rw [this]; exact h.1 _
end

theorem X
(n : ℕ)
(npos : n ≥ 1)
(veryodd : Matrix (Fin n) (Fin n) ℤ → Prop)
(hveryodd : ∀ A, veryodd A ↔ ∀ m ∈ Set.Icc 1 n, ∀ reind : Fin m → Fin n, Function.Injective reind → Odd (A.submatrix reind reind).det)
: ∀ A, veryodd A → (∀ k ≥ 1, veryodd (A ^ k)) := by
  intro A hA k hk
  rw [hveryodd] at hA
  let f := Int.castRingHom (ZMod 2)
  let B := A.map f
  have hodd : ∀ z : ℤ, Odd z → (z : ZMod 2) = 1 := by
    rintro z ⟨c, rfl⟩
    push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this]; simp
  have hodd' : ∀ z : ℤ, (z : ZMod 2) = 1 → Odd z := by
    intro z hz
    by_contra h
    rw [Int.not_odd_iff_even] at h
    obtain ⟨c, rfl⟩ := h
    push_cast at hz
    rw [CharTwo.add_self_eq_zero] at hz
    exact zero_ne_one hz
  have hdet : ∀ (C : Matrix (Fin n) (Fin n) ℤ) m (reind : Fin m → Fin n),
      ((C.submatrix reind reind).det : ZMod 2) = det ((C.map f).submatrix reind reind) := by
    intro C m reind
    have := f.map_det (C.submatrix reind reind)
    rw [RingHom.mapMatrix_apply] at this; exact this
  have H : ∀ S : Finset (Fin n), S.Nonempty →
      det (B.submatrix (fun x : S => x.1) (fun x : S => x.1)) = 1 := by
    intro S hS
    let e := (Fintype.equivFin S).symm
    have hc : 1 ≤ Fintype.card S := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hS
    have hc2 : Fintype.card S ≤ n := by
      rw [Fintype.card_coe]; simpa using Finset.card_le_univ S
    have := hA (Fintype.card S) ⟨hc, hc2⟩ (fun a => (e a).1)
      (fun a b h => e.injective (Subtype.ext h))
    have h2 := hodd _ this
    rw [hdet] at h2
    rw [← h2, ← Matrix.det_submatrix_equiv_self e]
    rfl
  have hs := sink_lem B H
  obtain ⟨r, hinj, hedge⟩ := rank_lem B hs n Finset.univ (by simp)
  have hr : Function.Injective r := fun a b h => hinj (Finset.mem_coe.mpr (Finset.mem_univ a))
    (Finset.mem_coe.mpr (Finset.mem_univ b)) h
  have hT : Tri r B := ⟨diag_one B H, fun i j hij hne => hedge i (Finset.mem_univ _) j (Finset.mem_univ _) (Ne.symm hij) hne⟩
  have hTk := (hT.pow k)
  rw [hveryodd]
  intro m _ reind hre
  apply hodd'
  rw [hdet]
  have : (A ^ k).map f = B ^ k := by
    have := map_pow f.mapMatrix A k
    simpa [RingHom.mapMatrix_apply] using this
  rw [this]
  exact Tri.det hr hTk reind hre
