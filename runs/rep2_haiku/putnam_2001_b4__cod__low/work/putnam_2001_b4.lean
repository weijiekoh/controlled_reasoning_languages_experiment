import Mathlib

open Topology Filter Polynomial Set

noncomputable abbrev putnam_2001_b4_solution : Prop := True
/--
Let $S$ denote the set of rational numbers different from $\{-1,0,1\}$.  Define $f:S\rightarrow S$ by $f(x)=x-1/x$. Prove or disprove that \[\bigcap_{n=1}^\infty f^{(n)}(S) = \emptyset,\] where $f^{(n)}$ denotes $f$ composed with itself $n$ times.
-/
theorem putnam_2001_b4
(S : Set ℚ)
(hS : S = univ \ {-1, 0, 1})
(f : S → S)
(hf : ∀ x : S, f x = x - 1 / (x : ℚ))
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution := by
  have arith : ∀ p q : ℤ, p ≠ 0 → 1 ≤ q → (p.natAbs : ℤ) ≠ q →
      p.natAbs + q.natAbs + 1 ≤ (p^2 - q^2).natAbs + (p*q).natAbs := by
    intro p q hp hq hne
    have hA : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp
    lift q to ℕ using (by omega)
    have hsq : (p^2 - (q:ℤ)^2).natAbs = ((p.natAbs:ℤ)^2 - (q:ℤ)^2).natAbs := by
      rw [← Int.natAbs_sq p]
    rw [Int.natAbs_mul, hsq]
    simp only [Int.natAbs_natCast] at *
    generalize p.natAbs = A at *
    have hA' : (1:ℤ) ≤ A := by exact_mod_cast hA
    have hne' : (A:ℤ) ≠ q := hne
    have hq' : (1:ℤ) ≤ q := by exact_mod_cast hq
    have main : (A:ℤ) + q + 1 ≤ (((A:ℤ)^2 - q^2).natAbs : ℤ) + (A:ℤ) * q := by
      rcases lt_or_gt_of_ne hne' with h | h
      · have hneg : (A:ℤ)^2 - q^2 < 0 := by nlinarith
        have hB : (((A:ℤ)^2 - q^2).natAbs : ℤ) = q^2 - A^2 := by
          rw [Int.ofNat_natAbs_of_nonpos hneg.le]; ring
        rw [hB]
        nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ q - A by omega) (show (0:ℤ) ≤ q + A by omega)]
      · have hpos : (A:ℤ)^2 - q^2 > 0 := by nlinarith
        have hB : (((A:ℤ)^2 - q^2).natAbs : ℤ) = A^2 - q^2 := by
          rw [Int.natAbs_of_nonneg hpos.le]
        rw [hB]
        nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ A - q by omega) (show (0:ℤ) ≤ q + A by omega)]
    exact_mod_cast main
  have gen : ∀ a b : ℤ, 0 < b → Int.gcd a b = 1 →
      ((a:ℚ)/(b:ℚ)).num.natAbs + ((a:ℚ)/(b:ℚ)).den = a.natAbs + b.natAbs := by
    intro a b hb h
    have hc : Nat.Coprime a.natAbs b.natAbs := h
    have h1 := Rat.num_div_eq_of_coprime hb hc
    have h2 := Rat.den_div_eq_of_coprime hb hc
    rw [h1]
    have h3 : b.natAbs = ((a/b : ℚ).den) := by omega
    omega
  have key : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x hx0 hx1 hxm1
    have hp0 : x.num ≠ 0 := Rat.num_ne_zero.mpr hx0
    have hxeq : x = (x.num:ℚ)/((x.den:ℤ):ℚ) := by
      push_cast; exact (Rat.num_div_den x).symm
    have hcop : Int.gcd x.num (x.den:ℤ) = 1 := by
      have := x.reduced
      unfold Int.gcd
      simpa using this
    have hne0 : (x.num.natAbs : ℤ) ≠ (x.den : ℤ) := by
      intro h
      have h2 : x.num.natAbs = x.den := by exact_mod_cast h
      have h3 : x.den = 1 := by
        have := hcop
        unfold Int.gcd at this
        simp [h2] at this
        exact this
      have hp1 : x.num.natAbs = 1 := by rw [h2, h3]
      have hxv : x = (x.num : ℚ) := by rw [hxeq, h3]; simp
      rcases Int.natAbs_eq_iff.mp hp1 with h4 | h4
      · apply hx1; rw [hxv, h4]; norm_num
      · apply hxm1; rw [hxv, h4]; norm_num
    generalize hp : x.num = p at *
    generalize hq : x.den = q at *
    have hq1 : (1:ℤ) ≤ q := by exact_mod_cast (show 0 < q from hq ▸ x.pos)
    have hpq : IsCoprime p (q:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hNp : IsCoprime (p^2 - (q:ℤ)^2) p := by
      obtain ⟨u, v, h⟩ := hpq.pow_right (n := 2)
      exact ⟨-v, u + v*p, by linear_combination h⟩
    have hNq : IsCoprime (p^2 - (q:ℤ)^2) (q:ℤ) := by
      obtain ⟨u, v, h⟩ := hpq.symm.pow_right (n := 2)
      exact ⟨v, u + v*q, by linear_combination h⟩
    have hg1 : Int.gcd (p^2 - (q:ℤ)^2) (p*q) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right hNp hNq)
    have hp0' : (p:ℚ) ≠ 0 := by exact_mod_cast hp0
    have hq0' : (q:ℚ) ≠ 0 := by
      have : (0:ℚ) < q := by exact_mod_cast (show (0:ℤ) < q by omega)
      exact this.ne'
    have hval : x - 1/x = (((p^2 - (q:ℤ)^2 : ℤ)):ℚ) / (((p*q : ℤ)):ℚ) := by
      rw [hxeq]; push_cast; field_simp
    have hD0 : p * (q:ℤ) ≠ 0 := mul_ne_zero hp0 (by omega)
    have hne : (p.natAbs : ℤ) ≠ (q:ℤ) := by
      intro h
      have h2 : p.natAbs = q := by exact_mod_cast h
      have h3 : q = 1 := by
        have := hcop
        unfold Int.gcd at this
        simp [h2] at this
        exact_mod_cast this
      have hp1 : p.natAbs = 1 := by omega
      have hxv : x = (p : ℚ) := by rw [hxeq, h3]; simp
      rcases Int.natAbs_eq_iff.mp hp1 with h4 | h4
      · apply hx1; rw [hxv, h4]; norm_num
      · apply hxm1; rw [hxv, h4]; norm_num
    have hAr := arith p q hp0 hq1 hne
    rcases lt_or_gt_of_ne hD0 with hn | hpos
    · have e : x - 1/x = ((-(p^2 - (q:ℤ)^2) : ℤ):ℚ) / ((-(p*q) : ℤ):ℚ) := by
        rw [hval, Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
      rw [e, gen _ _ (by omega) (by have := hg1; unfold Int.gcd at this ⊢; rw [Int.natAbs_neg, Int.natAbs_neg]; exact this)]
      rw [Int.natAbs_neg, Int.natAbs_neg]
      simp only [Int.natAbs_natCast] at *
      omega
    · rw [hval, gen _ _ hpos hg1]
      simp only [Int.natAbs_natCast] at *
      omega
  have hyS : ∀ y : S, (y:ℚ) ≠ 0 ∧ (y:ℚ) ≠ 1 ∧ (y:ℚ) ≠ -1 := by
    intro y
    have hy : (y:ℚ) ∈ univ \ {-1, 0, 1} := by rw [← hS]; exact y.2
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, mem_univ, true_and, not_or] at hy
    exact ⟨hy.2.1, hy.2.2, hy.1⟩
  have iter : ∀ n : ℕ, ∀ y : S, (y:ℚ).num.natAbs + (y:ℚ).den + n ≤
      ((f^[n] y : S) : ℚ).num.natAbs + ((f^[n] y : S) : ℚ).den := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply']
      have h1 := ih y
      have h2 := key ((f^[k] y : S) : ℚ) (hyS _).1 (hyS _).2.1 (hyS _).2.2
      rw [hf]
      omega
  refine iff_of_true ?_ trivial
  ext z
  simp only [mem_iInter, mem_image, mem_Ici, mem_univ, true_and, mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨x, hx⟩ := h ((z:ℚ).num.natAbs + (z:ℚ).den + 1) (by omega)
  have h1 := iter ((z:ℚ).num.natAbs + (z:ℚ).den + 1) x
  rw [hx] at h1
  have h2 : 0 < x.1.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hyS x).1)
  have h3 : 0 < (x.1:ℚ).den := (x.1:ℚ).pos
  omega
