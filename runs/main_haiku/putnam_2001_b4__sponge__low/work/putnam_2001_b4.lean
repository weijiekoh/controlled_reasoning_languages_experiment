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

  have arith : ∀ p q : ℤ, 0 < q → p ≠ 0 → p.natAbs ≠ q.natAbs →
      (p^2 - q^2).natAbs + (p*q).natAbs ≥ p.natAbs + q.natAbs + 1 := by
    intro p q hq hp hne
    have hA : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp
    have hQ : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq.ne'
    have hAQ : (p.natAbs : ℤ) ≠ (q.natAbs : ℤ) := by exact_mod_cast hne
    have e : p^2 - q^2 = (p.natAbs:ℤ)^2 - (q.natAbs:ℤ)^2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]
    have key : ((p.natAbs:ℤ) + (q.natAbs:ℤ)) ≤ |(p.natAbs:ℤ)^2 - (q.natAbs:ℤ)^2| := by
      have hA' : (1:ℤ) ≤ p.natAbs := by exact_mod_cast hA
      have hQ'' : (1:ℤ) ≤ q.natAbs := by exact_mod_cast hQ
      rcases lt_or_gt_of_ne hAQ with h | h
      · rw [abs_of_nonpos (by nlinarith)]
        nlinarith
      · rw [abs_of_nonneg (by nlinarith)]
        nlinarith
    have h2 : ((p^2-q^2).natAbs : ℤ) = |(p.natAbs:ℤ)^2 - (q.natAbs:ℤ)^2| := by
      rw [e, Int.natCast_natAbs]
    have h3 : p.natAbs + q.natAbs ≤ (p^2-q^2).natAbs := by
      have : ((p.natAbs + q.natAbs : ℕ):ℤ) ≤ ((p^2-q^2).natAbs:ℤ) := by
        rw [Nat.cast_add, h2]; exact key
      exact_mod_cast this
    rw [Int.natAbs_mul]
    nlinarith [h3, hA, hQ]
  have num_den : ∀ a b : ℤ, b ≠ 0 → Nat.Coprime a.natAbs b.natAbs →
      ((a:ℚ)/(b:ℚ)).num.natAbs = a.natAbs ∧ ((a:ℚ)/(b:ℚ)).den = b.natAbs := by
    have pos : ∀ a b : ℤ, 0 < b → Nat.Coprime a.natAbs b.natAbs →
        ((a:ℚ)/(b:ℚ)).num.natAbs = a.natAbs ∧ ((a:ℚ)/(b:ℚ)).den = b.natAbs := by
      intro a b hb h
      have h1 := Rat.num_div_eq_of_coprime hb h
      have h2 := Rat.den_div_eq_of_coprime hb h
      refine ⟨by rw [h1], ?_⟩
      have : (((a:ℚ)/(b:ℚ)).den : ℤ) = (b.natAbs : ℤ) := by
        rw [h2]; exact (Int.natAbs_of_nonneg hb.le).symm
      exact_mod_cast this
    intro a b hb h
    rcases lt_or_gt_of_ne hb with hb' | hb'
    · have e : (a:ℚ)/(b:ℚ) = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by
        push_cast; rw [neg_div_neg_eq]
      rw [e]
      have := pos (-a) (-b) (by omega) (by simpa [Int.natAbs_neg] using h)
      simpa [Int.natAbs_neg] using this
    · exact pos a b hb' h
  have aux : ∀ p q : ℚ, p ≠ 0 → q ≠ 0 → p/q - 1/(p/q) = (p^2-q^2)/(p*q) := by
    intro p q hp hq
    field_simp
  have step : ∀ z : ℚ, z ≠ 0 → z ≠ 1 → z ≠ -1 →
      z.num.natAbs + z.den + 1 ≤ (z - 1/z).num.natAbs + (z - 1/z).den := by
    intro z h0 h1 h2
    have hp0 : z.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hqpos : (0:ℤ) < z.den := by exact_mod_cast z.den_pos
    have hcop : IsCoprime z.num (z.den:ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      have := z.reduced
      simpa [Int.gcd] using this
    have hne : z.num.natAbs ≠ (z.den:ℤ).natAbs := by
      intro h
      have hd1 : z.den = 1 := by
        have := z.reduced
        rw [Int.natAbs_natCast] at h
        rw [h] at this
        simpa using this
      have hz : z = (z.num : ℚ) := by
        have := Rat.num_div_den z
        rw [hd1] at this
        simpa using this.symm
      have hn : z.num = 1 ∨ z.num = -1 := by
        have : z.num.natAbs = 1 := by
          rw [Int.natAbs_natCast] at h
          omega
        omega
      rcases hn with h' | h'
      · exact h1 (by rw [hz, h']; norm_num)
      · exact h2 (by rw [hz, h']; norm_num)
    have hzq : z = (z.num:ℚ)/(z.den:ℚ) := (Rat.num_div_den z).symm
    have hp' : (z.num:ℚ) ≠ 0 := by exact_mod_cast hp0
    have hq' : (z.den:ℚ) ≠ 0 := by exact_mod_cast z.den_pos.ne'
    have hq : (z - 1/z) = (((z.num^2 - (z.den:ℤ)^2 : ℤ)):ℚ) / (((z.num * (z.den:ℤ)) : ℤ):ℚ) := by
      have := aux (z.num:ℚ) (z.den:ℚ) hp' hq'
      rw [← hzq] at this
      push_cast
      exact this
    rw [hq]
    have hcop2 : IsCoprime (z.num^2 - (z.den:ℤ)^2) (z.num * (z.den:ℤ)) := by
      apply IsCoprime.mul_right
      · have h1 : IsCoprime (-((z.den:ℤ)^2)) z.num := (hcop.symm.pow_left).neg_left
        have := h1.add_mul_left_left z.num
        have e : z.num^2 - (z.den:ℤ)^2 = -((z.den:ℤ)^2) + z.num * z.num := by ring
        rw [e]; exact this
      · have h1 : IsCoprime (z.num^2) (z.den:ℤ) := hcop.pow_left
        have := h1.add_mul_left_left (-(z.den:ℤ))
        have e : z.num^2 - (z.den:ℤ)^2 = z.num^2 + (z.den:ℤ) * (-(z.den:ℤ)) := by ring
        rw [e]; exact this
    obtain ⟨e1, e2⟩ := num_den (z.num^2 - (z.den:ℤ)^2) (z.num * (z.den:ℤ))
      (mul_ne_zero hp0 hqpos.ne') (Int.isCoprime_iff_gcd_eq_one.mp hcop2)
    rw [e1, e2]
    have hA := arith z.num (z.den:ℤ) hqpos hp0 hne
    have hd : (z.den:ℤ).natAbs = z.den := Int.natAbs_natCast _
    rw [hd] at hA
    linarith
  have hf' : ∀ x : S, ((f x : S) : ℚ) = (x:ℚ) - 1/(x:ℚ) := by
    intro x; rw [hf x]
  have hmem : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ) ≠ 1 ∧ (x:ℚ) ≠ -1 := by
    intro x
    have hx : (x:ℚ) ∈ S := x.2
    simp only [hS, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_and, not_or] at hx
    exact ⟨hx.2.1, hx.2.2, hx.1⟩
  have iter : ∀ n : ℕ, ∀ x : S,
      (x:ℚ).num.natAbs + (x:ℚ).den + n ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      have h1 := ih x
      have hy := step ((f^[k] x : S):ℚ) (hmem _).1 (hmem _).2.1 (hmem _).2.2
      rw [← hf' (f^[k] x)] at hy
      linarith
  refine iff_of_true ?_ trivial
  ext y
  simp only [Set.mem_iInter, Set.mem_image, Set.mem_Ici, Set.mem_univ, true_and, Set.mem_empty_iff_false, iff_false]
  intro h
  have hN : 1 ≤ (y:ℚ).num.natAbs + (y:ℚ).den := by
    have := (y:ℚ).den_pos
    omega
  obtain ⟨x, hx⟩ := h _ hN
  have h1 := iter ((y:ℚ).num.natAbs + (y:ℚ).den) x
  rw [hx] at h1
  have hxd := (x:ℚ).den_pos
  omega
