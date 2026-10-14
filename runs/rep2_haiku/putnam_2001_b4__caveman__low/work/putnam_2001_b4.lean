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
  have gen : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b →
      ((a:ℚ)/(b:ℚ)).num.natAbs + ((a:ℚ)/(b:ℚ)).den = a.natAbs + b.natAbs := by
    have pos : ∀ a b : ℤ, 0 < b → IsCoprime a b →
        ((a:ℚ)/(b:ℚ)).num.natAbs + ((a:ℚ)/(b:ℚ)).den = a.natAbs + b.natAbs := by
      intro a b hb hc
      have hcop : a.natAbs.Coprime b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc
      have hn := Rat.num_div_eq_of_coprime hb hcop
      have hd := Rat.den_div_eq_of_coprime hb hcop
      rw [hn]
      have : ((a:ℚ)/(b:ℚ)).den = b.natAbs := by
        have h2 : (((a:ℚ)/(b:ℚ)).den : ℤ) = b := hd
        omega
      rw [this]
    intro a b hb hc
    rcases lt_or_gt_of_ne hb with h | h
    · have e : (a:ℚ)/(b:ℚ) = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by
        push_cast; rw [neg_div_neg_eq]
      rw [e, pos (-a) (-b) (by omega) (hc.neg_left.neg_right)]
      simp [Int.natAbs_neg]
    · exact pos a b h hc
  have ineq : ∀ A B : ℤ, 1 ≤ A → 1 ≤ B → A ≠ B → A + B + 1 ≤ |A^2 - B^2| + A*B := by
    intro A B hA hB hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_nonpos (by nlinarith)]
      nlinarith
    · rw [abs_of_nonneg (by nlinarith)]
      nlinarith
  have key : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x h0 h1 h2
    have hp : (x.num : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr h0
    have hq : (x.den : ℚ) ≠ 0 := by positivity
    have hqpos : (1:ℤ) ≤ (x.den : ℤ) := by exact_mod_cast x.den_pos
    have hxe : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    have hy : x - 1/x = (((x.num^2 - (x.den:ℤ)^2 : ℤ)) : ℚ) / ((x.num * (x.den:ℤ) : ℤ) : ℚ) := by
      conv_lhs => rw [hxe]
      push_cast
      field_simp
    have hcop0 : IsCoprime x.num (x.den : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using x.reduced)
    have hq2 : IsCoprime ((x.den:ℤ)^2) x.num := hcop0.symm.pow_left
    have hp2 : IsCoprime ((x.num)^2) (x.den:ℤ) := hcop0.pow_left
    have c1 : IsCoprime (x.num^2 - (x.den:ℤ)^2) x.num := by
      have h := (IsCoprime.neg_left hq2).add_mul_left_left x.num
      have e : (-((x.den:ℤ)^2) + x.num * x.num) = x.num^2 - (x.den:ℤ)^2 := by ring
      rw [e] at h; exact h
    have c2 : IsCoprime (x.num^2 - (x.den:ℤ)^2) (x.den:ℤ) := by
      have h := (IsCoprime.neg_left hp2).add_mul_left_left (x.den:ℤ)
      have e : (-((x.num)^2) + (x.den:ℤ) * (x.den:ℤ)) = -(x.num^2 - (x.den:ℤ)^2) := by ring
      rw [e] at h
      exact (IsCoprime.neg_left_iff _ _).mp h
    have hc : IsCoprime (x.num^2 - (x.den:ℤ)^2) (x.num * (x.den:ℤ)) :=
      IsCoprime.mul_right c1 c2
    have hp0 : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hb : x.num * (x.den:ℤ) ≠ 0 := mul_ne_zero hp0 (by omega)
    rw [hy, gen _ _ hb hc]
    have hne : |x.num| ≠ (x.den:ℤ) := by
      intro he
      have hq0 : (0:ℤ) ≤ (x.den:ℤ) := by positivity
      rcases (abs_eq hq0).mp he with e | e
      · apply h1
        have e2 : (x.num:ℚ) = (x.den:ℚ) := by exact_mod_cast e
        rw [← Rat.num_div_den x, e2, div_self hq]
      · apply h2
        have e2 : (x.num:ℚ) = -(x.den:ℚ) := by exact_mod_cast e
        rw [← Rat.num_div_den x, e2, neg_div, div_self hq]
    have I := ineq |x.num| (x.den:ℤ) (Int.one_le_abs hp0) hqpos hne
    simp only [sq_abs] at I
    have H : ((x.num.natAbs : ℕ) : ℤ) + ((x.den : ℕ) : ℤ) + 1 ≤
        (((x.num^2 - (x.den:ℤ)^2)).natAbs : ℤ) + ((x.num * (x.den:ℤ)).natAbs : ℤ) := by
      have e1 : ((x.num^2 - (x.den:ℤ)^2).natAbs : ℤ) = |x.num^2 - (x.den:ℤ)^2| := Int.natCast_natAbs _
      have e2 : ((x.num * (x.den:ℤ)).natAbs : ℤ) = |x.num| * (x.den:ℤ) := by
        rw [Int.natCast_natAbs, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (x.den:ℤ))]
      have e3 : ((x.num.natAbs : ℕ) : ℤ) = |x.num| := Int.natCast_natAbs _
      rw [e1, e2, e3]
      linarith
    exact_mod_cast H
  have hempty : ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro y hy
    simp only [mem_iInter, mem_image, mem_univ, true_and, mem_Ici] at hy
    have hmem : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ) ≠ 1 ∧ (x:ℚ) ≠ -1 := by
      intro x
      have hx0 : (x:ℚ) ∈ univ \ ({-1, 0, 1} : Set ℚ) := by rw [← hS]; exact x.2
      have hx : (x:ℚ) ∉ ({-1, 0, 1} : Set ℚ) := hx0.2
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
      exact ⟨hx.2.1, hx.2.2, hx.1⟩
    have step : ∀ x : S, (x:ℚ).num.natAbs + (x:ℚ).den + 1 ≤ ((f x : S):ℚ).num.natAbs + ((f x : S):ℚ).den := by
      intro x
      obtain ⟨h0, h1, h2⟩ := hmem x
      rw [hf x]
      exact key _ h0 h1 h2
    have iter : ∀ n : ℕ, ∀ x : S, (x:ℚ).num.natAbs + (x:ℚ).den + n ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ k ih =>
        intro x
        have h1 := ih x
        have h2 := step (f^[k] x)
        rw [Function.iterate_succ_apply']
        omega
    obtain ⟨x, hx⟩ := hy ((y:ℚ).num.natAbs + (y:ℚ).den + 1) (by omega)
    have h3 := iter ((y:ℚ).num.natAbs + (y:ℚ).den + 1) x
    rw [hx] at h3
    have h4 : 1 ≤ (x:ℚ).num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hmem x).1)
    have h5 : 1 ≤ (x:ℚ).den := (x:ℚ).den_pos
    omega
  simp only [putnam_2001_b4_solution, iff_true]
  exact hempty
