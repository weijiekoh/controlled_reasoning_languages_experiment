import Mathlib

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

end gen
