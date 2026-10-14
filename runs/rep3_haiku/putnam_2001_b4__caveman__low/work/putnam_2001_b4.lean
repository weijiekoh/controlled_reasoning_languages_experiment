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
  have ineq : ∀ p q : ℤ, 0 < q → p ≠ 0 → p ≠ q → p ≠ -q →
      p.natAbs + q.natAbs + 2 ≤ (p*p-q*q).natAbs + (p*q).natAbs := by
    intro p q hq hp0 hpq1 hpq2
    have ha : 1 ≤ |p| := Int.one_le_abs hp0
    have hne : |p| ≠ q := by
      intro h
      rcases abs_choice p with h1 | h1
      · exact hpq1 (by linarith)
      · exact hpq2 (by linarith)
    have hpp : p * p = |p| * |p| := (abs_mul_abs_self p).symm
    have hD : |p * q| = |p| * q := by rw [abs_mul, abs_of_pos hq]
    rw [← Int.ofNat_le]
    push_cast [Int.natCast_natAbs]
    rw [hpp, hD, abs_of_pos hq]
    generalize |p| = a at *
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_neg (show a * a - q * q < 0 by nlinarith)]
      nlinarith
    · rw [abs_of_nonneg (show 0 ≤ a * a - q * q by nlinarith)]
      nlinarith
  have gen : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b →
      ((a:ℚ)/b).num.natAbs + ((a:ℚ)/b).den = a.natAbs + b.natAbs := by
    intro a b hb hc
    have hc2 : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc
    rcases lt_or_gt_of_ne hb with hb' | hb'
    · have e : (a:ℚ)/b = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by push_cast; rw [neg_div_neg_eq]
      have h1 : 0 < -b := by omega
      have h2 : Nat.Coprime (-a).natAbs (-b).natAbs := by simpa using hc2
      have hn := Rat.num_div_eq_of_coprime h1 h2
      have hd := Rat.den_div_eq_of_coprime h1 h2
      rw [e, hn]
      have hd' : (((((-a:ℤ):ℚ)/((-b:ℤ):ℚ))).den : ℤ) = -b := hd
      simp only [Int.natAbs_neg] at *
      omega
    · have h1 : 0 < b := hb'
      have hn := Rat.num_div_eq_of_coprime h1 hc2
      have hd := Rat.den_div_eq_of_coprime h1 hc2
      rw [hn]
      omega
  have key : ∀ p q : ℤ, 0 < q → IsCoprime p q → p ≠ 0 → p ≠ q → p ≠ -q →
      p.natAbs + q.natAbs + 2 ≤ ((p:ℚ)/q - 1/((p:ℚ)/q)).num.natAbs
        + ((p:ℚ)/q - 1/((p:ℚ)/q)).den := by
    intro p q hq hcop hp0 hpq1 hpq2
    have hq0 : q ≠ 0 := ne_of_gt hq
    have hq0' : (q:ℚ) ≠ 0 := by exact_mod_cast hq0
    have hp0' : (p:ℚ) ≠ 0 := by exact_mod_cast hp0
    have hy : (p:ℚ)/q - 1/((p:ℚ)/q) = ((p*p-q*q : ℤ):ℚ) / ((p*q : ℤ):ℚ) := by
      push_cast
      field_simp
    have hNp : IsCoprime (p*p-q*q) p := by
      have hqqp : IsCoprime (q*q) p := (hcop.symm).mul_left hcop.symm
      obtain ⟨a, b, hab⟩ := hqqp.neg_left
      exact ⟨a, b - a*p, by linear_combination hab⟩
    have hNq : IsCoprime (p*p-q*q) q := by
      obtain ⟨a, b, hab⟩ := hcop.mul_left hcop
      exact ⟨a, b + a*q, by linear_combination hab⟩
    have hc2 : IsCoprime (p*p-q*q) (p*q) := hNp.mul_right hNq
    rw [hy, gen (p*p-q*q) (p*q) (mul_ne_zero hp0 hq0) hc2]
    exact ineq p q hq hp0 hpq1 hpq2
  have hmain : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den + 2 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x h0 h1 hm1
    have hcop : IsCoprime x.num (x.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
    have hq : (0:ℤ) < x.den := by exact_mod_cast x.den_pos
    have hxq : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by
      push_cast; exact (Rat.num_div_den x).symm
    have hp0 : x.num ≠ 0 := by
      intro h; apply h0; rw [hxq, h]; simp
    have hpq1 : x.num ≠ (x.den:ℤ) := by
      intro h
      rw [h] at hcop
      have hu := Int.isUnit_iff.mp (isCoprime_self.mp hcop)
      have hq1 : (x.den:ℤ) = 1 := by omega
      apply h1; rw [hxq, h, hq1]; norm_num
    have hpq2 : x.num ≠ -(x.den:ℤ) := by
      intro h
      rw [h] at hcop
      have hc : IsCoprime (x.den:ℤ) (x.den:ℤ) := (IsCoprime.neg_left_iff _ _).mp hcop
      have hu := Int.isUnit_iff.mp (isCoprime_self.mp hc)
      have hq1 : (x.den:ℤ) = 1 := by omega
      apply hm1; rw [hxq, h, hq1]; norm_num
    have := key x.num x.den hq hcop hp0 hpq1 hpq2
    rw [← hxq] at this
    simpa using this

  have hiter : ∀ n : ℕ, ∀ x : S, (x:ℚ).num.natAbs + (x:ℚ).den + 2*n
      ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hxS : (x:ℚ) ∈ univ \ {-1, 0, 1} := by rw [← hS]; exact x.2
      simp only [Set.mem_sdiff, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, not_or] at hxS
      obtain ⟨hm1, h0, h1⟩ := hxS
      have hfx : ((f x : S):ℚ) = (x:ℚ) - 1/(x:ℚ) := by rw [hf x]
      rw [Function.iterate_succ_apply]
      have h2 := ih (f x)
      rw [hfx] at h2
      have h3 := hmain x h0 h1 hm1
      omega
  simp only [putnam_2001_b4_solution, iff_true]
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  simp only [mem_iInter, mem_image, mem_univ, true_and, mem_Ici] at hy
  obtain ⟨x, hx⟩ := hy ((y:ℚ).num.natAbs + (y:ℚ).den + 1) (by omega)
  have h4 := hiter ((y:ℚ).num.natAbs + (y:ℚ).den + 1) x
  rw [hx] at h4
  omega
