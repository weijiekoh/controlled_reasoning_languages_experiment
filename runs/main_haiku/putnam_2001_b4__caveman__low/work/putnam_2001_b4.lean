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
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution :=
by
  classical
  subst hS
  obtain ⟨H, hH⟩ : ∃ H : ℚ → ℕ, ∀ x, H x = x.num.natAbs + x.den :=
    ⟨fun x => x.num.natAbs + x.den, fun _ => rfl⟩
  have hfrac : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b →
      ((a:ℚ)/b).num.natAbs + ((a:ℚ)/b).den = a.natAbs + b.natAbs := by
    intro a b hb hc
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · have e : (a:ℚ)/b = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by push_cast; rw [neg_div_neg_eq]
      have hc' : IsCoprime (-a) (-b) := hc.neg_left.neg_right
      have hg' : Nat.Coprime (-a).natAbs (-b).natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc'
      have hn := Rat.num_div_eq_of_coprime (a := -a) (b := -b) (by omega) hg'
      have hd := Rat.den_div_eq_of_coprime (a := -a) (b := -b) (by omega) hg'
      rw [e, hn]
      have : (((-a:ℤ):ℚ)/((-b:ℤ):ℚ)).den = (-b).natAbs := by omega
      rw [this]; simp [Int.natAbs_neg]
    · have hg : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc
      have hn := Rat.num_div_eq_of_coprime (a := a) (b := b) hpos hg
      have hd := Rat.den_div_eq_of_coprime (a := a) (b := b) hpos hg
      rw [hn]
      have : (((a:ℚ)/(b:ℚ)).den) = b.natAbs := by omega
      rw [this]
  have arith : ∀ (n : ℤ) (q : ℕ), 1 ≤ q → 1 ≤ n.natAbs → n.natAbs ≠ q →
      n.natAbs + q < (n^2 - (q:ℤ)^2).natAbs + (n * (q:ℤ)).natAbs := by
    intro n q hq hm hne
    have hn2 : n^2 = ((n.natAbs:ℕ):ℤ)^2 := (Int.natAbs_sq n).symm
    have hnq : (n * (q:ℤ)).natAbs = n.natAbs * q := by rw [Int.natAbs_mul]; simp
    rw [hnq, hn2]
    generalize n.natAbs = m at *
    have hne' : (m:ℤ) ≠ q := by exact_mod_cast hne
    have hm' : (1:ℤ) ≤ m := by exact_mod_cast hm
    have hq' : (1:ℤ) ≤ q := by exact_mod_cast hq
    have ht : (m:ℤ)+q ≤ (((m:ℤ)^2 - (q:ℤ)^2).natAbs : ℤ) := by
      rcases Int.natAbs_eq ((m:ℤ)^2 - (q:ℤ)^2) with h|h <;>
        rcases lt_or_gt_of_ne hne' with hlt|hgt <;> nlinarith
    have : (m:ℤ)+q < (((m:ℤ)^2 - (q:ℤ)^2).natAbs : ℤ) + m*q := by nlinarith
    exact_mod_cast this
  have step : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 → H x < H (x - 1/x) := by
    intro x h0 h1 h2
    have hp0 : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hcop : IsCoprime x.num (x.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
    have hpq : IsCoprime (x.num^2 - (x.den:ℤ)^2) (x.num * (x.den:ℤ)) := by
      obtain ⟨u2, v2, h2'⟩ := hcop.pow_right (n := 2)
      obtain ⟨u3, v3, h3'⟩ := hcop.symm.pow_right (n := 2)
      apply IsCoprime.mul_right
      · exact ⟨-v2, v2 * x.num + u2, by linear_combination h2'⟩
      · exact ⟨v3, v3 * (x.den:ℤ) + u3, by linear_combination h3'⟩
    have heq : x - 1/x = (((x.num^2 - (x.den:ℤ)^2 : ℤ)):ℚ) / (((x.num * (x.den:ℤ)) : ℤ):ℚ) := by
      have hqq : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
      have hpp : (x.num:ℚ) ≠ 0 := by exact_mod_cast hp0
      have hx : x = (x.num:ℚ)/(x.den:ℚ) := (Rat.num_div_den x).symm
      generalize x.num = p at hpp hx ⊢
      generalize x.den = q at hqq hx ⊢
      subst hx

      push_cast
      field_simp
    have hPQ : x.num.natAbs ≠ x.den := by
      intro hE
      have hg := x.reduced
      rw [hE] at hg
      have hd1 : x.den = 1 := by simpa [Nat.Coprime] using hg
      have hxn : x = (x.num : ℚ) := by
        have := Rat.num_div_den x
        rw [hd1] at this
        simpa using this.symm
      rcases (by omega : x.num = 1 ∨ x.num = -1) with h | h
      · exact h1 (by rw [hxn, h]; norm_num)
      · exact h2 (by rw [hxn, h]; norm_num)
    rw [hH, hH, heq, hfrac _ _ (by simpa using hp0) hpq]
    exact arith x.num x.den (Nat.one_le_iff_ne_zero.mpr x.den_nz)
      (Int.natAbs_pos.mpr hp0) hPQ
  have step' : ∀ z : (Set.Elem (univ \ ({-1, 0, 1} : Set ℚ))), H (z:ℚ) + 1 ≤ H ((f z : (Set.Elem (univ \ ({-1, 0, 1} : Set ℚ)))):ℚ) := by
    intro z
    have hz : (z:ℚ) ∈ univ \ ({-1, 0, 1} : Set ℚ) := z.2
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, not_or] at hz
    rw [hf z]
    have := step z hz.2.1 hz.2.2 hz.1
    omega
  have iter : ∀ k : ℕ, ∀ z : (Set.Elem (univ \ ({-1, 0, 1} : Set ℚ))), H (z:ℚ) + k ≤ H ((f^[k] z : (Set.Elem (univ \ ({-1, 0, 1} : Set ℚ)))):ℚ) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply]
      have h1 := ih (f z)
      have h2 := step' z

      omega
  have hempty : ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    simp only [mem_iInter, mem_Ici, mem_image, mem_univ, true_and] at hy
    obtain ⟨x, hx⟩ := hy (H (y:ℚ) + 1) (by omega)
    have := iter (H (y:ℚ) + 1) x
    rw [hx] at this
    omega
  exact iff_of_true hempty trivial
