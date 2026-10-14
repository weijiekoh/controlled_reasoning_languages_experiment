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
  simp only [putnam_2001_b4_solution, iff_true]

  have aux_ineq : ∀ p q : ℤ, 1 ≤ q → p ≠ 0 → p^2 ≠ q^2 → |p| + q + 1 ≤ |p^2 - q^2| + |p*q| := by
    intro p q hq hp hne
    have hA : 0 < |p| := abs_pos.mpr hp
    have hsq : |p|^2 = p^2 := sq_abs p
    have hne' : |p| ≠ q := by
      intro h; apply hne; rw [← hsq, h]
    have hqa : |q| = q := abs_of_nonneg (by omega)
    have h2 : |p| + q ≤ |p^2 - q^2| := by
      rw [← hsq]
      generalize |p| = A at hA hne' ⊢
      rcases lt_or_gt_of_ne hne' with h | h
      · rw [abs_of_neg (by nlinarith)]; nlinarith
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have h3 : 1 ≤ |p*q| := by
      rw [abs_mul, hqa]
      have : 1 ≤ |p| := by omega
      nlinarith
    linarith
  have H_div : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b → ((a:ℚ)/(b:ℚ)).num.natAbs + ((a:ℚ)/(b:ℚ)).den = a.natAbs + b.natAbs := by
    intro a b hb hc
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · have e : (a:ℚ)/(b:ℚ) = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by
        push_cast; rw [neg_div_neg_eq]
      rw [e]
      have hc' : IsCoprime (-a) (-b) := (hc.neg_left).neg_right
      have hcop : Nat.Coprime (-a).natAbs (-b).natAbs :=
        Int.isCoprime_iff_gcd_eq_one.mp hc'
      have hpos' : 0 < -b := by omega
      have hn := Rat.num_div_eq_of_coprime hpos' hcop
      have hd := Rat.den_div_eq_of_coprime hpos' hcop
      have hb' : ((-b).natAbs : ℤ) = -b := Int.natAbs_of_nonneg hpos'.le
      have hd2 : (((-a:ℤ):ℚ)/((-b:ℤ):ℚ)).den = (-b).natAbs := by omega
      rw [hn, hd2]
      simp [Int.natAbs_neg]
    · have hcop : Nat.Coprime a.natAbs b.natAbs :=
        Int.isCoprime_iff_gcd_eq_one.mp hc
      have hn := Rat.num_div_eq_of_coprime hpos hcop
      have hd := Rat.den_div_eq_of_coprime hpos hcop
      have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hpos.le
      have hd2 : ((a:ℚ)/(b:ℚ)).den = b.natAbs := by omega
      rw [hn, hd2]
  have step_int : ∀ p q : ℤ, 1 ≤ q → p ≠ 0 → IsCoprime p q → p^2 ≠ q^2 →
      ((p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ))).num.natAbs + ((p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ))).den ≥ p.natAbs + q.natAbs + 1 := by
    intro p q hq hp hcop hne
    obtain ⟨u, v, huv⟩ := hcop
    have hq0 : (q:ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hp0 : (p:ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp
    have c1 : IsCoprime (p^2-q^2) p :=
      ⟨-v^2, (u^2+v^2)*p + 2*u*v*q, by linear_combination (u*p+v*q+1)*huv⟩
    have c2 : IsCoprime (p^2-q^2) q :=
      ⟨u^2, 2*u*v*p + (u^2+v^2)*q, by linear_combination (u*p+v*q+1)*huv⟩
    have hc : IsCoprime (p^2-q^2) (p*q) := IsCoprime.mul_right c1 c2
    have hpq0 : p*q ≠ 0 := mul_ne_zero hp (by omega)
    have e : (p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ)) = ((p^2-q^2 : ℤ):ℚ)/((p*q:ℤ):ℚ) := by
      push_cast; field_simp; try ring
    rw [e, H_div _ _ hpq0 hc]
    have h := aux_ineq p q hq hp hne
    have hqa : |q| = q := abs_of_nonneg (by omega)
    have h4 : ((p^2-q^2).natAbs : ℤ) = |p^2-q^2| := Int.natCast_natAbs _
    have h5 : ((p*q).natAbs : ℤ) = |p*q| := Int.natCast_natAbs _
    have h6 : ((p.natAbs : ℕ) : ℤ) = |p| := Int.natCast_natAbs _
    have h7 : ((q.natAbs : ℕ) : ℤ) = q := by omega
    omega
  have step_Q : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 → x.num.natAbs + x.den + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x h0 h1 h2
    have hx : ((x.num:ℚ)/((x.den:ℤ):ℚ)) = x := by push_cast; exact Rat.num_div_den x
    have hcop : IsCoprime x.num (x.den:ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
    have hq : 1 ≤ (x.den:ℤ) := by have := x.den_pos; omega
    have hp : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hne : x.num^2 ≠ (x.den:ℤ)^2 := by
      intro h
      have h' : (x.num - x.den) * (x.num + x.den) = 0 := by linear_combination h
      have key : (x.den:ℤ) = 1 ∧ (x.num = 1 ∨ x.num = -1) := by
        rcases mul_eq_zero.mp h' with h'' | h''
        · have hpe : x.num = x.den := by linarith
          rw [hpe] at hcop
          have hu := Int.isUnit_iff.mp (isCoprime_self.mp hcop)
          omega
        · have hpe : x.num = -x.den := by linarith
          rw [hpe] at hcop
          have hc2 : IsCoprime (x.den:ℤ) (x.den:ℤ) := by simpa using hcop.neg_left
          have hu := Int.isUnit_iff.mp (isCoprime_self.mp hc2)
          omega
      obtain ⟨hd1, hn⟩ := key
      rw [hd1] at hx
      norm_num at hx
      rcases hn with hn | hn
      · exact h1 (by rw [← hx, hn]; norm_num)
      · exact h2 (by rw [← hx, hn]; norm_num)
    have key := step_int x.num x.den hq hp hcop hne
    rw [hx] at key
    have e : ((x.den:ℤ)).natAbs = x.den := by simp
    rw [e] at key
    omega
  have step_S : ∀ y : S, (y:ℚ).num.natAbs + (y:ℚ).den + 1 ≤ ((f y : S):ℚ).num.natAbs + ((f y : S):ℚ).den := by
    intro y
    have hy : (y:ℚ) ∈ univ \ ({-1,0,1}:Set ℚ) := by subst hS; exact y.2

    simp only [Set.mem_sdiff, mem_univ, mem_insert_iff, mem_singleton_iff, true_and, not_or] at hy
    have hfy : ((f y : S):ℚ) = (y:ℚ) - 1/(y:ℚ) := by rw [hf y]
    rw [hfy]
    exact step_Q _ hy.2.1 hy.2.2 hy.1
  have iter : ∀ n : ℕ, ∀ y : S, (y:ℚ).num.natAbs + (y:ℚ).den + n ≤ ((f^[n] y : S):ℚ).num.natAbs + ((f^[n] y : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply']
      have h1 := step_S (f^[n] y)
      have h2 := ih y
      push_cast
      omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨y, -, hy⟩ := (Set.mem_iInter₂.mp hz ((z:ℚ).num.natAbs + (z:ℚ).den + 1)
    (Set.mem_Ici.mpr (by omega)))
  have := iter ((z:ℚ).num.natAbs + (z:ℚ).den + 1) y
  rw [hy] at this
  omega
