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
  -- reduced-height formula for a coprime quotient
  have key0 : ∀ p q : ℤ, 0 < q → IsCoprime p q →
      (((p:ℚ)/(q:ℚ)).num.natAbs + ((p:ℚ)/(q:ℚ)).den) = p.natAbs + q.natAbs := by
    intro p q hq hpq
    have hc : Nat.Coprime p.natAbs q.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hpq
    have hn := Rat.num_div_eq_of_coprime hq hc
    have hd := Rat.den_div_eq_of_coprime hq hc
    have hd' : (((p:ℚ)/(q:ℚ)).den : ℤ) = q := hd
    have : ((p:ℚ)/(q:ℚ)).den = q.natAbs := by omega
    rw [hn, this]
  have key : ∀ p q : ℤ, q ≠ 0 → IsCoprime p q →
      (((p:ℚ)/(q:ℚ)).num.natAbs + ((p:ℚ)/(q:ℚ)).den) = p.natAbs + q.natAbs := by
    intro p q hq hpq
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · have e : (p:ℚ)/(q:ℚ) = (-p:ℤ)/((-q:ℤ):ℚ) := by push_cast; rw [neg_div_neg_eq]
      rw [e, key0 (-p) (-q) (by omega) (hpq.neg_left.neg_right)]
      simp [Int.natAbs_neg]
    · exact key0 p q hpos hpq
  -- the height goes up by at least one under f
  have alg : ∀ (a B : ℤ) (y : ℚ), y = (a:ℚ)/(B:ℚ) → a ≠ 0 → B ≠ 0 →
      y - 1/y = (((a^2-B^2 : ℤ)):ℚ)/(((a*B : ℤ)):ℚ) := by
    intro a B y hy ha hB
    subst hy
    have ha' : (a:ℚ) ≠ 0 := by exact_mod_cast ha
    have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB
    push_cast
    field_simp
  have final : ∀ A D : ℕ, 1 ≤ A → 1 ≤ D → A ≠ D →
      A + D + 1 ≤ ((A:ℤ)^2-(D:ℤ)^2).natAbs + A*D := by
    intro A D hA hD hne
    have hN : ((((A:ℤ)^2-(D:ℤ)^2).natAbs : ℕ) : ℤ) = |(A:ℤ)^2-(D:ℤ)^2| := Int.natCast_natAbs _
    have hA' : (1:ℤ) ≤ A := by exact_mod_cast hA
    have hD' : (1:ℤ) ≤ D := by exact_mod_cast hD
    have hne' : (A:ℤ) ≠ D := by exact_mod_cast hne
    have main : (A:ℤ)+D+1 ≤ |(A:ℤ)^2-(D:ℤ)^2| + A*D := by
      rcases lt_or_gt_of_ne hne' with h | h
      · have h2 : (A:ℤ) + 1 ≤ D := by omega
        rw [abs_of_neg (by nlinarith)]
        nlinarith
      · have h2 : (D:ℤ) + 1 ≤ A := by omega
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
    have : ((A + D + 1 : ℕ) : ℤ) ≤ ((((A:ℤ)^2-(D:ℤ)^2).natAbs + A*D : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hstep : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x h0 h1 h2
    have hcop : IsCoprime x.num (x.den:ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using x.reduced)
    have hxe : x = (x.num:ℚ)/((x.den:ℤ):ℚ) := by
      push_cast; exact (Rat.num_div_den x).symm
    have hden : ((x.den:ℤ):ℚ) ≠ 0 := by exact_mod_cast x.den_nz
    have ha0 : x.num ≠ 0 := by
      intro h; apply h0; rw [hxe, h]; simp
    have hB0 : (x.den:ℤ) ≠ 0 := by exact_mod_cast x.den_nz
    have hab : x.num.natAbs ≠ x.den := by
      intro h
      have h' : x.num.natAbs = (x.den:ℤ).natAbs := by simpa using h
      rcases Int.natAbs_eq_natAbs_iff.mp h' with h3 | h3
      · apply h1; rw [hxe, h3]; field_simp
      · apply h2; rw [hxe, h3]; push_cast; field_simp
    have hcopF : IsCoprime (x.num^2 - (x.den:ℤ)^2) (x.num * (x.den:ℤ)) := by
      obtain ⟨u, v, huv⟩ := hcop
      have c1 : IsCoprime (x.num^2 - (x.den:ℤ)^2) x.num :=
        ⟨-v^2, u^2*x.num+2*u*v*(x.den:ℤ) + v^2*x.num, by linear_combination (u*x.num+v*(x.den:ℤ)+1)*huv⟩
      have c2 : IsCoprime (x.num^2 - (x.den:ℤ)^2) (x.den:ℤ) :=
        ⟨u^2, u^2*(x.den:ℤ)+2*u*v*x.num + v^2*(x.den:ℤ), by linear_combination (u*x.num+v*(x.den:ℤ)+1)*huv⟩
      exact c1.mul_right c2
    rw [alg _ _ x hxe ha0 hB0, key _ _ (mul_ne_zero ha0 hB0) hcopF, Int.natAbs_mul]
    have := final x.num.natAbs x.den (Nat.pos_of_ne_zero (by simpa using ha0))
      x.den_pos (by exact hab)
    have hsq : (x.num.natAbs : ℤ)^2 = x.num^2 := Int.natAbs_sq _
    have e : (x.num^2 - (x.den:ℤ)^2).natAbs = ((x.num.natAbs:ℤ)^2-(x.den:ℤ)^2).natAbs := by
      rw [hsq]
    have e2 : ((x.den:ℤ)).natAbs = x.den := by simp
    rw [e, e2]
    omega
  have hiter : ∀ n : ℕ, ∀ x : S,
      (x:ℚ).num.natAbs + (x:ℚ).den + n ≤ ((f^[n] x : S) : ℚ).num.natAbs + ((f^[n] x : S) : ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      have hx := x.2
      have hx' : (x:ℚ) ∈ univ \ ({-1, 0, 1} : Set ℚ) := by rw [← hS]; exact hx
      simp only [Set.mem_sdiff, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, not_or] at hx'
      obtain ⟨h2, h0, h1⟩ := hx'
      have h := hstep x h0 h1 h2
      have hi := ih (f x)
      rw [hf x] at hi
      omega
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro y hy
  obtain ⟨x, -, hxy⟩ := mem_iInter₂.mp hy ((y:ℚ).num.natAbs + (y:ℚ).den + 1)
    (by simp)
  have hi := hiter ((y:ℚ).num.natAbs + (y:ℚ).den + 1) x
  rw [hxy] at hi
  omega
