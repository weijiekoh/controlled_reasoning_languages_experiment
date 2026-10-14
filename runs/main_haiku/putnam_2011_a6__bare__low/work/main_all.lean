import Mathlib
open Topology Filter Matrix

section gen
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma ch_sum_eq (z : H) : ∑ ψ : AddChar H ℂ, ψ z = if z = 0 then (Fintype.card H : ℂ) else 0 := by
  rw [AddChar.sum_apply_eq_ite]

lemma ch_inv (F : H → ℂ) (x : H) :
    ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, F y * ψ y = (Fintype.card H : ℂ) * F x := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ y, ∑ ψ : AddChar H ℂ, ψ (-x) * (F y * ψ y)
      = F y * (if y = x then (Fintype.card H : ℂ) else 0) := by
    intro y
    have h1 : ∀ ψ : AddChar H ℂ, ψ (-x) * (F y * ψ y) = F y * ψ (y + -x) := by
      intro ψ; rw [AddChar.map_add_eq_mul]; ring
    have h2 : ∑ ψ : AddChar H ℂ, ψ (y + -x) = if y = x then (Fintype.card H : ℂ) else 0 := by
      simp [ch_sum_eq, add_neg_eq_zero]
    simp only [h1]
    rw [← Finset.mul_sum, h2]
  rw [Finset.sum_congr rfl (fun y _ => h y)]
  simp [mul_ite, mul_comm]

lemma ch_prod {ι : Type*} (ψ : AddChar H ℂ) (g : ι → H) (s : Finset ι) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma parseval (Q : H → ℝ) :
    ∑ x, (Q x) ^ 2 = (1 / (Fintype.card H : ℝ)) * ∑ ψ : AddChar H ℂ, ‖∑ y, (Q y : ℂ) * ψ y‖ ^ 2 := by
  have hpos : (0 : ℝ) < Fintype.card H := by
    have : Nonempty H := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hQ : ∀ x, (Q x : ℂ) = (1 / (Fintype.card H : ℂ)) * ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, (Q y : ℂ) * ψ y := by
    intro x
    rw [ch_inv]
    field_simp
  have hconj : ∀ ψ : AddChar H ℂ, ∑ x, (Q x : ℂ) * ψ (-x)
      = starRingEnd ℂ (∑ y, (Q y : ℂ) * ψ y) := by
    intro ψ
    simp only [map_sum, map_mul, Complex.conj_ofReal, ← AddChar.inv_apply_eq_conj, AddChar.map_neg_eq_inv]
  have e1 : ∀ x, (Q x : ℂ) ^ 2 = ∑ ψ : AddChar H ℂ, (1 / (Fintype.card H : ℂ)) * ((Q x : ℂ) * ψ (-x)) * ∑ y, (Q y : ℂ) * ψ y := by
    intro x
    calc (Q x : ℂ) ^ 2 = (Q x : ℂ) * ((1 / (Fintype.card H : ℂ)) * ∑ ψ : AddChar H ℂ, ψ (-x) * ∑ y, (Q y : ℂ) * ψ y) := by
          rw [← hQ x]; ring
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intros; ring
  have e2 : ∀ ψ : AddChar H ℂ, ∑ x, (1 / (Fintype.card H : ℂ)) * ((Q x : ℂ) * ψ (-x)) * ∑ y, (Q y : ℂ) * ψ y
      = (1 / (Fintype.card H : ℂ)) * (starRingEnd ℂ (∑ y, (Q y : ℂ) * ψ y) * ∑ y, (Q y : ℂ) * ψ y) := by
    intro ψ
    rw [← hconj ψ, Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have e3 : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj']; norm_cast
  have key : ((∑ x, (Q x) ^ 2 : ℝ) : ℂ) = (((1 / (Fintype.card H : ℝ)) * ∑ ψ : AddChar H ℂ, ‖∑ y, (Q y : ℂ) * ψ y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
    simp only [e2]
    rw [← Finset.mul_sum]
    simp only [e3]
    push_cast
    rfl
  exact_mod_cast key


lemma count_transform {ι : Type*} [Fintype ι] (g : ι → H) (m : ℕ) (ψ : AddChar H ℂ) :
    ∑ y, ((Finset.univ.filter (fun f : Fin m → ι => ∑ i, g (f i) = y)).card : ℂ) * ψ y
      = (∑ j, ψ (g j)) ^ m := by
  have h1 : ∀ y, ((Finset.univ.filter (fun f : Fin m → ι => ∑ i, g (f i) = y)).card : ℂ) * ψ y
      = ∑ f : Fin m → ι, if ∑ i, g (f i) = y then ψ y else 0 := by
    intro y
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ f : Fin m → ι, ∑ y, (if ∑ i, g (f i) = y then ψ y else 0) = ψ (∑ i, g (f i)) := by
    intro f; rw [Finset.sum_ite_eq]; simp
  simp only [h2, ch_prod]
  have h3 := Fintype.prod_sum (fun (_ : Fin m) (j : ι) => ψ (g j))
  rw [show (∑ j, ψ (g j)) ^ m = ∏ _i : Fin m, ∑ j, ψ (g j) by simp [Finset.prod_const], h3]

lemma norm_sub_sq_re (z w : ℂ) : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 - 2 * (starRingEnd ℂ w * z).re + ‖w‖ ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma lam_lt_one {ι : Type*} [Fintype ι] (g : ι → H) (i0 : ι) (hi0 : g i0 = 0)
    (hgen : ∀ ψ : AddChar H ℂ, (∀ i, ψ (g i) = 1) → ψ = 0)
    (ψ : AddChar H ℂ) (hψ : ψ ≠ 0) (hk : 0 < Fintype.card ι) :
    ‖(∑ j, ψ (g j)) / (Fintype.card ι : ℂ)‖ < 1 := by
  by_contra hcon
  push_neg at hcon
  set k : ℂ := (Fintype.card ι : ℂ) with hkdef
  have hk0 : k ≠ 0 := by rw [hkdef]; exact_mod_cast hk.ne'
  set s := ∑ j, ψ (g j) with hs
  set lam := s / k with hlam
  have hsk : s = lam * k := by rw [hlam]; field_simp
  have hnorm_le : ‖lam‖ ≤ 1 := by
    rw [hlam, norm_div]
    have : ‖s‖ ≤ ∑ j, ‖ψ (g j)‖ := norm_sum_le _ _
    simp only [AddChar.norm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [hkdef, Complex.norm_natCast, div_le_one (by exact_mod_cast hk)]
    exact this
  have hnorm1 : ‖lam‖ = 1 := le_antisymm hnorm_le hcon
  -- sum of squared distances is zero
  have hsum : ∑ j, ‖ψ (g j) - lam‖ ^ 2 = 0 := by
    have hre : ∑ j, (starRingEnd ℂ lam * ψ (g j)).re = (starRingEnd ℂ lam * s).re := by
      rw [hs, Finset.mul_sum, Complex.re_sum]
    have hcalc : (starRingEnd ℂ lam * s).re = (Fintype.card ι : ℝ) := by
      rw [hsk]
      have : starRingEnd ℂ lam * (lam * k) = ((‖lam‖ ^ 2 : ℝ) : ℂ) * k := by
        rw [← mul_assoc, mul_comm (starRingEnd ℂ lam) lam, Complex.mul_conj']
        push_cast; ring
      rw [this, hnorm1, hkdef]; simp
    have hterm : ∀ j, ‖ψ (g j) - lam‖ ^ 2 = 1 - 2 * (starRingEnd ℂ lam * ψ (g j)).re + ‖lam‖ ^ 2 := by
      intro j
      rw [norm_sub_sq_re, AddChar.norm_apply]; ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hre, hcalc, hnorm1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hall : ∀ j, ψ (g j) - lam = 0 := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hsum j (Finset.mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hlam1 : lam = 1 := by
    have h0 := hall i0
    rw [hi0, AddChar.map_zero_eq_one, sub_eq_zero] at h0
    exact h0.symm
  apply hψ
  apply hgen
  intro i
  have := hall i
  rw [hlam1, sub_eq_zero] at this
  exact this


lemma S_formula {ι : Type*} [Fintype ι] (g : ι → H) (m : ℕ) (hk : 0 < Fintype.card ι)
    (P : H → ℝ) (hP : ∀ y, P y = ((Finset.univ.filter (fun f : Fin m → ι => ∑ i, g (f i) = y)).card : ℝ)
        / (Fintype.card ι : ℝ) ^ m) :
    ∑ x : H, (P x - 1 / (Fintype.card H : ℝ)) ^ 2
      = (1 / (Fintype.card H : ℝ)) * ∑ ψ : AddChar H ℂ,
          if ψ = 0 then 0 else ‖(∑ j, ψ (g j)) / (Fintype.card ι : ℂ)‖ ^ (2 * m) := by
  classical
  rw [parseval]
  congr 1
  apply Finset.sum_congr rfl
  intro ψ _
  have hk' : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hn' : (Fintype.card H : ℂ) ≠ 0 := by
    have : Nonempty H := ⟨0⟩
    exact_mod_cast Fintype.card_pos.ne'
  have h5 : ∀ y, ((P y - 1 / (Fintype.card H : ℝ) : ℝ) : ℂ) * ψ y
      = ((Finset.univ.filter (fun f : Fin m → ι => ∑ i, g (f i) = y)).card : ℂ)
          / (Fintype.card ι : ℂ) ^ m * ψ y - (1 / (Fintype.card H : ℂ)) * ψ y := by
    intro y; rw [hP y]; push_cast; ring
  have hT : ∑ y, ((P y - 1 / (Fintype.card H : ℝ) : ℝ) : ℂ) * ψ y
      = ((∑ j, ψ (g j)) / (Fintype.card ι : ℂ)) ^ m
        - (1 / (Fintype.card H : ℂ)) * ∑ y, ψ y := by
    simp only [h5, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, count_transform, div_pow]
  rw [hT, AddChar.sum_eq_ite]
  by_cases h0 : ψ = 0
  · subst h0
    simp only [if_true, AddChar.zero_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have e : (Fintype.card ι : ℂ) * 1 / (Fintype.card ι : ℂ) = 1 := by rw [mul_one, div_self hk']
    rw [e, one_pow, one_div_mul_cancel hn', sub_self, norm_zero]; norm_num
  · simp only [h0, if_false, if_false, mul_zero, sub_zero]
    rw [norm_pow, ← pow_mul, mul_comm]


lemma asymp {X : Type*} [Fintype X] [DecidableEq X] (z0 : X) (r : X → ℝ) (hr0 : ∀ x, 0 ≤ r x)
    (hr1 : ∀ x, x ≠ z0 → r x < 1) (hpos : ∃ x, x ≠ z0 ∧ 0 < r x) (n : ℝ) (hn : 0 < n) :
    ∃ b ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0, Tendsto (fun m : ℕ => (1 / b ^ (2 * m)) *
      ((1 / n) * ∑ x, if x = z0 then 0 else r x ^ (2 * m))) atTop (𝓝 C) := by
  obtain ⟨x1, hx1, hr1pos⟩ := hpos
  set S := Finset.univ.filter (fun x => x ≠ z0) with hSdef
  have hS : S.Nonempty := ⟨x1, by simp [S, hx1]⟩
  obtain ⟨xs, hxsS, hxsb⟩ := Finset.exists_mem_eq_sup' hS r
  have hxs : xs ≠ z0 := by simpa [S] using hxsS
  have hle : ∀ x, x ≠ z0 → r x ≤ S.sup' hS r := fun x hx =>
    Finset.le_sup' r (by simp [S, hx])
  set b := S.sup' hS r with hbdef
  have hb0 : 0 < b := lt_of_lt_of_le hr1pos (hle x1 hx1)
  have hb1 : b < 1 := by rw [hxsb]; exact hr1 xs hxs
  have hxsb' : r xs = b := hxsb.symm
  refine ⟨b, ⟨hb0, hb1⟩, (1 / n) * ((Finset.univ.filter (fun x => x ≠ z0 ∧ r x = b)).card : ℝ), ?_, ?_⟩
  · apply mul_pos (by positivity)
    exact_mod_cast Finset.card_pos.mpr (⟨xs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs, hxsb'⟩⟩ : (Finset.univ.filter (fun x => x ≠ z0 ∧ r x = b)).Nonempty)
  · set f : X → ℕ → ℝ := fun x m => (1 / b ^ (2 * m)) * (if x = z0 then 0 else r x ^ (2 * m)) with hf
    have hrewrite : ∀ m : ℕ, (1 / b ^ (2 * m)) * ((1 / n) * ∑ x, if x = z0 then 0 else r x ^ (2 * m))
        = (1 / n) * ∑ x, f x m := by
      intro m
      simp only [hf, Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
    simp only [hrewrite]
    have hfx : ∀ x, Tendsto (fun m => f x m) atTop
        (𝓝 (if x ≠ z0 ∧ r x = b then (1 : ℝ) else 0)) := by
      intro x
      by_cases hx : x = z0
      · have : (if x ≠ z0 ∧ r x = b then (1 : ℝ) else 0) = 0 := by simp [hx]
        rw [this]
        have : (fun m => f x m) = fun _ => (0 : ℝ) := by
          funext m; simp [hf, hx]
        rw [this]; exact tendsto_const_nhds
      by_cases hxb : r x = b
      · have : (if x ≠ z0 ∧ r x = b then (1 : ℝ) else 0) = 1 := by simp [hx, hxb]
        rw [this]
        have : (fun m => f x m) = fun _ => (1 : ℝ) := by
          funext m
          simp only [hf, if_neg hx, hxb]
          have : b ^ (2 * m) ≠ 0 := pow_ne_zero _ hb0.ne'
          field_simp
        rw [this]; exact tendsto_const_nhds
      · have hlt : r x < b := lt_of_le_of_ne (hle x hx) hxb
        have : (if x ≠ z0 ∧ r x = b then (1 : ℝ) else 0) = 0 := by simp [hxb]
        rw [this]
        have hq : (fun m => f x m) = fun m => ((r x / b) ^ 2) ^ m := by
          funext m
          simp only [hf, if_neg hx]
          rw [← pow_mul, div_pow, one_div_mul_eq_div]
        rw [hq]
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · positivity
        · have h0 : 0 ≤ r x / b := div_nonneg (hr0 x) hb0.le
          have h1 : r x / b < 1 := (div_lt_one hb0).2 hlt
          nlinarith
    have hsum := tendsto_finset_sum (Finset.univ) (fun x _ => hfx x)
    have hC := hsum.const_mul (1 / n)
    convert hC using 2
    rw [Finset.sum_boole]



theorem putnam_2011_a6_aux
(G : Type*) [CommGroup G] [Fintype G]
(n : ℕ)
(gset : Set G)
(k : ℕ)
(mgprob : ℕ → G → ℝ)
(hmgprob : mgprob = (fun (m : ℕ) (x : G) => ({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ) / k ^ m))
(hn : n = (Fintype.elems : Finset G).card)
(hk : gset.encard = k)
(hgsetprop : k < n)
(hgset1 : 1 ∈ gset)
(hgsetgen : Subgroup.closure gset = ⊤)
: ∃ b ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0, Tendsto (fun m : ℕ => (1 / b ^ (2 * m)) * (∑ x : G, (mgprob m x - 1 / n) ^ 2)) atTop (𝓝 C) := by
  classical
  subst hmgprob
  have hfin : gset.Finite := Set.finite_of_encard_eq_coe hk
  have : Fintype gset := hfin.fintype
  have hkn : gset.ncard = k := by
    have h2 := hfin.cast_ncard_eq
    rw [hk] at h2
    exact_mod_cast h2
  have hcard : Fintype.card gset = k := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hkn]
  have hkpos : 0 < Fintype.card gset := Fintype.card_pos_iff.mpr ⟨⟨1, hgset1⟩⟩
  have hnN : n = Fintype.card G := by rw [hn]; exact Finset.card_univ
  have hnR : (n : ℝ) = (Fintype.card G : ℝ) := by rw [hnN]
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcnt : ∀ (m : ℕ) (x : G), ({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ)
      = ((Finset.univ.filter (fun f : Fin m → gset =>
          ∑ i, Additive.ofMul ((f i).1 : G) = Additive.ofMul x)).card : ℝ) := by
    intro m x
    congr 1
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    congr 1
  -- the generator map
  set g : gset → Additive G := fun s => Additive.ofMul (s : G) with hg
  have hS : ∀ m : ℕ, ∑ x : G, ((({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ)
        / (k : ℝ) ^ m) - 1 / (n : ℝ)) ^ 2
      = (1 / (n : ℝ)) * ∑ ψ : AddChar (Additive G) ℂ,
          if ψ = 0 then 0 else ‖(∑ j, ψ (g j)) / (Fintype.card gset : ℂ)‖ ^ (2 * m) := by
    intro m
    have e := S_formula g m hkpos (fun y => ((Finset.univ.filter (fun f : Fin m → gset =>
        ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ m) (fun y => rfl)
    have e2 : ∑ x : G, ((({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ)
        / (k : ℝ) ^ m) - 1 / (n : ℝ)) ^ 2
        = ∑ y : Additive G, ((((Finset.univ.filter (fun f : Fin m → gset =>
            ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ m) - 1 / (Fintype.card (Additive G) : ℝ)) ^ 2 := by
      rw [Fintype.card_additive, hnR]
      trans ∑ x : G, ((((Finset.univ.filter (fun f : Fin m → gset =>
            ∑ i, g (f i) = Additive.ofMul x)).card : ℝ) / (Fintype.card gset : ℝ) ^ m) - 1 / (Fintype.card G : ℝ)) ^ 2
      · apply Finset.sum_congr rfl
        intro x _
        rw [hcnt m x, hcard]
      · exact Equiv.sum_comp Additive.ofMul (fun y => ((((Finset.univ.filter (fun f : Fin m → gset =>
            ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ m) - 1 / (Fintype.card G : ℝ)) ^ 2)
    rw [e2, e, Fintype.card_additive, hnR]
  -- existence of a nontrivial character with nonzero mean
  have hpos : ∃ ψ : AddChar (Additive G) ℂ, ψ ≠ 0 ∧
      0 < ‖(∑ j, ψ (g j)) / (Fintype.card gset : ℂ)‖ := by
    obtain ⟨x0, hx0⟩ : ∃ x0 : G, x0 ∉ gset := by
      by_contra hc
      push_neg at hc
      have hu : gset = Set.univ := Set.eq_univ_of_forall hc
      have h3 : gset.ncard = Nat.card G := by rw [hu, Set.ncard_univ]
      have hk' : k = Fintype.card G := by rw [← hkn, h3, Nat.card_eq_fintype_card]
      omega
    have hzero : ((Finset.univ.filter (fun f : Fin 1 → gset =>
        ∑ i, g (f i) = Additive.ofMul x0)).card : ℝ) = 0 := by
      have hem : Finset.univ.filter (fun f : Fin 1 → gset =>
          ∑ i, g (f i) = Additive.ofMul x0) = ∅ := by
        apply Finset.filter_false_of_mem
        intro f _ h
        rw [Fin.sum_univ_one] at h
        apply hx0
        have h' := Additive.ofMul.injective h
        rw [← h']
        exact (f 0).2
      rw [hem]; simp
    have h1 := S_formula g 1 hkpos (fun y => ((Finset.univ.filter (fun f : Fin 1 → gset =>
        ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ 1) (fun y => rfl)
    have hle : (0 - 1 / (Fintype.card (Additive G) : ℝ)) ^ 2 ≤
        ∑ y : Additive G, ((((Finset.univ.filter (fun f : Fin 1 → gset =>
          ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ 1) - 1 / (Fintype.card (Additive G) : ℝ)) ^ 2 := by
      have := Finset.single_le_sum (f := fun y : Additive G => ((((Finset.univ.filter (fun f : Fin 1 → gset =>
          ∑ i, g (f i) = y)).card : ℝ) / (Fintype.card gset : ℝ) ^ 1) - 1 / (Fintype.card (Additive G) : ℝ)) ^ 2)
        (fun y _ => sq_nonneg _) (Finset.mem_univ (Additive.ofMul x0))
      simpa only [hzero, zero_div] using this
    have hc : (0 : ℝ) < (Fintype.card (Additive G) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
    have hT : (∑ ψ : AddChar (Additive G) ℂ,
        if ψ = 0 then 0 else ‖(∑ j, ψ (g j)) / (Fintype.card gset : ℂ)‖ ^ (2 * 1)) ≠ 0 := by
      intro hT0
      rw [hT0, mul_zero] at h1
      rw [h1] at hle
      have hp : 0 < 1 / (Fintype.card (Additive G) : ℝ) := one_div_pos.mpr hc
      nlinarith [hp]
    obtain ⟨ψ, _, hψ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    by_cases hψ0 : ψ = 0
    · simp [hψ0] at hψ
    · refine ⟨ψ, hψ0, ?_⟩
      rw [if_neg hψ0] at hψ
      have hz : ‖(∑ j, ψ (g j)) / (Fintype.card gset : ℂ)‖ ≠ 0 := fun h => hψ (by rw [h]; norm_num)
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hgen : ∀ ψ : AddChar (Additive G) ℂ, (∀ i, ψ (g i) = 1) → ψ = 0 := by
    intro ψ hψ
    have hall : ∀ x : G, x ∈ Subgroup.closure gset → ψ (Additive.ofMul x) = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hψ ⟨x, hx⟩
      | one => exact AddChar.map_zero_eq_one ψ
      | mul x y _ _ ihx ihy =>
        show ψ (Additive.ofMul x + Additive.ofMul y) = 1
        rw [AddChar.map_add_eq_mul, ihx, ihy, mul_one]
      | inv x _ ih =>
        show ψ (-(Additive.ofMul x)) = 1
        rw [AddChar.map_neg_eq_inv, ih, inv_one]
    apply AddChar.ext
    intro a
    have hmem : Additive.toMul a ∈ Subgroup.closure gset := by
      rw [hgsetgen]; exact Subgroup.mem_top _
    have h := hall _ hmem
    rw [AddChar.zero_apply]
    exact h
  obtain ⟨ψ0, hψ0, hψ0pos⟩ := hpos
  obtain ⟨b, hb, C, hC, hT⟩ := asymp (0 : AddChar (Additive G) ℂ)
    (fun ψ => ‖(∑ j, ψ (g j)) / (Fintype.card gset : ℂ)‖) (fun ψ => norm_nonneg _)
    (fun ψ hψ => lam_lt_one g ⟨1, hgset1⟩ rfl hgen ψ hψ hkpos) ⟨ψ0, hψ0, hψ0pos⟩ (n : ℝ) hnpos
  refine ⟨b, hb, C, hC, ?_⟩
  refine Tendsto.congr (fun m => ?_) hT
  beta_reduce
  rw [hS m]

end gen
