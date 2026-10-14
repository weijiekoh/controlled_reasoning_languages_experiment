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
  subst hS
  have H_div : ∀ a b : ℤ, b ≠ 0 → Nat.Coprime a.natAbs b.natAbs →
      ((a:ℚ)/b).num.natAbs + ((a:ℚ)/b).den = a.natAbs + b.natAbs := by
    intro a b hb h
    rcases lt_or_gt_of_ne hb with hb' | hb'
    · have e : (a:ℚ)/b = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by
        rw [Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
      have hc : Nat.Coprime (-a).natAbs (-b).natAbs := by
        rw [Int.natAbs_neg, Int.natAbs_neg]; exact h
      rw [e, Rat.num_div_eq_of_coprime (by omega) hc]
      have hd := Rat.den_div_eq_of_coprime (by omega : (0:ℤ) < -b) hc
      have n1 : (-a).natAbs = a.natAbs := Int.natAbs_neg a
      have n2 : (-b).natAbs = b.natAbs := Int.natAbs_neg b
      rw [n1]
      omega
    · rw [Rat.num_div_eq_of_coprime hb' h]
      have hd := Rat.den_div_eq_of_coprime hb' h
      omega
  have key2 : ∀ (p : ℤ) (D : ℕ), p ≠ 0 → 0 < D → Nat.Coprime p.natAbs D →
      ¬ (p.natAbs = 1 ∧ D = 1) →
      (((p:ℚ)/D) - 1/((p:ℚ)/D)).num.natAbs + (((p:ℚ)/D) - 1/((p:ℚ)/D)).den
        ≥ p.natAbs + D + 1 := by
    intro p D hp hD hc hne
    have hq : (D:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp
    have hb : p * (D:ℤ) ≠ 0 := mul_ne_zero hp (by exact_mod_cast hD.ne')
    have hval : (p:ℚ)/D - 1/((p:ℚ)/D) = ((p^2 - (D:ℤ)^2 : ℤ):ℚ) / ((p * (D:ℤ) : ℤ):ℚ) := by
      push_cast
      field_simp
    have hcop1 : IsCoprime p (D:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hc
    obtain ⟨u, v, hu⟩ := hcop1
    have hcop : IsCoprime (p^2 - (D:ℤ)^2) (p * (D:ℤ)) :=
      ⟨u^2 * (1 + (u^2+v^2)*(D:ℤ)^2) - (u^2+v^2)^2 * (D:ℤ)^2,
       2*u*v*(1 + (u^2+v^2)*(D:ℤ)^2) + (u^2+v^2)^2 * (p * (D:ℤ)), by
        linear_combination (1 + u*p + v*(D:ℤ)) * (1 + (u^2+v^2)*(D:ℤ)^2) * hu⟩
    have hc2 : Nat.Coprime (p^2 - (D:ℤ)^2).natAbs (p * (D:ℤ)).natAbs :=
      Int.isCoprime_iff_gcd_eq_one.mp hcop
    rw [hval, H_div _ _ hb hc2]
    have hPD : (p * (D:ℤ)).natAbs = p.natAbs * D := by
      rw [Int.natAbs_mul]; simp
    rw [hPD]
    have e : ((p.natAbs:ℤ))^2 = p^2 := Int.natAbs_sq p
    have hsq : ((p^2 - (D:ℤ)^2).natAbs : ℤ) ≥ (p.natAbs:ℤ)^2 - (D:ℤ)^2 := by
      linarith [@Int.le_natAbs (p^2 - (D:ℤ)^2)]
    have hsq2 : ((p^2 - (D:ℤ)^2).natAbs : ℤ) ≥ (D:ℤ)^2 - (p.natAbs:ℤ)^2 := by
      have := @Int.le_natAbs (-(p^2 - (D:ℤ)^2))
      rw [Int.natAbs_neg] at this
      linarith
    have hP : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp
    have hD1 : 1 ≤ D := hD
    have hP' : (1:ℤ) ≤ p.natAbs := by exact_mod_cast hP
    have hD' : (1:ℤ) ≤ D := by exact_mod_cast hD1
    rcases lt_trichotomy p.natAbs D with h | h | h
    · have h' : (p.natAbs:ℤ) + 1 ≤ D := by exact_mod_cast h
      have key : (p.natAbs:ℤ) + D + 1 ≤ (p^2 - (D:ℤ)^2).natAbs + p.natAbs * D := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (by positivity : (0:ℤ) ≤ D + p.natAbs),
          mul_pos (by linarith : (0:ℤ) < p.natAbs) (by linarith : (0:ℤ) < D)]
      exact_mod_cast key
    · exfalso
      rw [h] at hc
      have hD1' : D = 1 := by simpa using hc
      exact hne ⟨by omega, hD1'⟩
    · have h' : (D:ℤ) + 1 ≤ p.natAbs := by exact_mod_cast h
      have key : (p.natAbs:ℤ) + D + 1 ≤ (p^2 - (D:ℤ)^2).natAbs + p.natAbs * D := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (by positivity : (0:ℤ) ≤ D + p.natAbs),
          mul_pos (by linarith : (0:ℤ) < p.natAbs) (by linarith : (0:ℤ) < D)]
      exact_mod_cast key
  have step : ∀ z : ↥(univ \ ({-1, 0, 1} : Set ℚ)), ((f z : ↥(univ \ ({-1, 0, 1} : Set ℚ))) : ℚ).num.natAbs + ((f z : ↥(univ \ ({-1, 0, 1} : Set ℚ))) : ℚ).den
      ≥ ((z : ℚ).num.natAbs + (z : ℚ).den) + 1 := by
    intro z
    rw [hf z]
    have hz := z.2
    have hz' : (z:ℚ) ≠ -1 ∧ (z:ℚ) ≠ 0 ∧ (z:ℚ) ≠ 1 := by
      simp only [Set.mem_sdiff, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, not_or] at hz; exact hz
    obtain ⟨h1, h0, h2⟩ := hz'
    have := key2 (z:ℚ).num (z:ℚ).den (Rat.num_ne_zero.mpr h0) (Rat.den_pos _)
      (Rat.reduced _) (by
        rintro ⟨ha, hb⟩
        have hz1 : (z:ℚ) = (z:ℚ).num / (z:ℚ).den := (Rat.num_div_den _).symm
        rw [hb] at hz1
        simp only [Nat.cast_one, div_one] at hz1
        rcases Int.natAbs_eq (z:ℚ).num with e | e <;> rw [ha] at e <;> push_cast at e
        · exact h2 (by rw [hz1, e]; norm_num)
        · exact h1 (by rw [hz1, e]; norm_num))
    rw [Rat.num_div_den] at this
    exact this
  have iter : ∀ n : ℕ, ∀ z : ↥(univ \ ({-1, 0, 1} : Set ℚ)), ((f^[n] z : ↥(univ \ ({-1, 0, 1} : Set ℚ))) : ℚ).num.natAbs + ((f^[n] z : ↥(univ \ ({-1, 0, 1} : Set ℚ))) : ℚ).den
      ≥ ((z : ℚ).num.natAbs + (z : ℚ).den) + n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply']
      have h1 := step (f^[k] z)
      have h2 := ih z
      omega
  have key : ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ := by
    ext y
    constructor
    · intro hy
      have h := (mem_iInter₂.mp hy) ((y:ℚ).num.natAbs + (y:ℚ).den + 1) (by simp)
      obtain ⟨x, _, hx⟩ := h
      have := iter ((y:ℚ).num.natAbs + (y:ℚ).den + 1) x
      rw [hx] at this
      omega
    · intro h
      simp at h
  rw [key]
  simp [putnam_2001_b4_solution]
