import Mathlib

open Topology Filter Polynomial Set

lemma aux_rat (N D : ℤ) (hD : D ≠ 0) (hc : IsCoprime N D) :
    ((N:ℚ)/(D:ℚ)).num.natAbs + ((N:ℚ)/(D:ℚ)).den = N.natAbs + D.natAbs := by
  have hcop : Nat.Coprime N.natAbs D.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc
  rcases lt_or_gt_of_ne hD with h | h
  · have e : (N:ℚ)/(D:ℚ) = ((-N:ℤ):ℚ)/((-D:ℤ):ℚ) := by push_cast; rw [neg_div_neg_eq]
    have hcop' : Nat.Coprime (-N).natAbs (-D).natAbs := by simpa [Int.natAbs_neg] using hcop
    have h1 := Rat.num_div_eq_of_coprime (a := -N) (b := -D) (by omega) hcop'
    have h2 := Rat.den_div_eq_of_coprime (a := -N) (b := -D) (by omega) hcop'
    rw [e, h1]
    have h3 : (((-N:ℤ):ℚ)/((-D:ℤ):ℚ)).den = (-D).natAbs := by
      have := h2; omega
    rw [h3, Int.natAbs_neg, Int.natAbs_neg]
  · have h1 := Rat.num_div_eq_of_coprime (a := N) (b := D) h hcop
    have h2 := Rat.den_div_eq_of_coprime (a := N) (b := D) h hcop
    rw [h1]
    have h3 : ((N:ℚ)/(D:ℚ)).den = D.natAbs := by
      have := h2; omega
    rw [h3]

lemma key_pq (x : ℚ) (p q : ℤ) (hq : 0 < q) (hx : x = (p:ℚ)/(q:ℚ)) (hc : IsCoprime p q)
    (hp : p ≠ 0) (hx2 : x^2 ≠ 1) :
    p.natAbs + q.natAbs + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
  subst hx
  have hp' : (p:ℚ) ≠ 0 := by exact_mod_cast hp
  have hq' : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsq : p^2 ≠ q^2 := by
    intro h; apply hx2
    have : (p:ℚ)^2 = (q:ℚ)^2 := by exact_mod_cast h
    rw [div_pow, this, div_self (pow_ne_zero _ hq')]
  have hD : (p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ)) = ((p^2-q^2 : ℤ):ℚ)/((p*q : ℤ):ℚ) := by
    push_cast; field_simp
  have hDne : p*q ≠ 0 := mul_ne_zero hp hq.ne'
  have hc1 : IsCoprime (p^2-q^2) p := by
    have h1 : IsCoprime (-(q^2)) p := (hc.symm.pow_left (m := 2)).neg_left
    have e : p^2 - q^2 = -(q^2) + p*p := by ring
    rw [e]; exact h1.add_mul_left_left p
  have hc2 : IsCoprime (p^2-q^2) q := by
    have h1 : IsCoprime (p^2) q := hc.pow_left
    have e : p^2 - q^2 = p^2 + q*(-q) := by ring
    rw [e]; exact h1.add_mul_left_left (-q)
  have hc3 : IsCoprime (p^2-q^2) (p*q) := hc1.mul_right hc2
  rw [hD, aux_rat _ _ hDne hc3, Int.natAbs_mul]
  have hA : ((p.natAbs:ℕ):ℤ)^2 = p^2 := Int.natAbs_sq p
  have hB : ((q.natAbs:ℕ):ℤ)^2 = q^2 := Int.natAbs_sq q
  have hAB : (p.natAbs:ℤ) ≠ (q.natAbs:ℤ) := by
    intro h; apply hsq; rw [← hA, ← hB, h]
  have hpa : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp
  have hqa : 1 ≤ q.natAbs := by omega
  have hN : p.natAbs + q.natAbs ≤ (p^2-q^2).natAbs := by
    have e : p^2 - q^2 = ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 := by rw [hA, hB]
    rw [e]
    rcases lt_or_gt_of_ne hAB with h | h
    · have : ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 ≤ -((p.natAbs:ℤ)+(q.natAbs:ℤ)) := by
        nlinarith
      omega
    · have : ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 ≥ ((p.natAbs:ℤ)+(q.natAbs:ℤ)) := by
        nlinarith
      omega
  have hM : 1 ≤ p.natAbs * q.natAbs := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

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
  have hmem : ∀ y : ℚ, y ∈ S ↔ (y ≠ -1 ∧ y ≠ 0 ∧ y ≠ 1) := by
    intro y; rw [hS]; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, mem_univ, true_and, not_or]
  have hS' : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ)^2 ≠ 1 := by
    intro x
    have hx := (hmem x).1 x.2
    obtain ⟨h1, h0, h2⟩ := hx
    refine ⟨h0, ?_⟩
    intro h
    rcases mul_eq_zero.mp (show ((x:ℚ)-1)*((x:ℚ)+1) = 0 by linear_combination h) with h' | h'
    · exact h2 (by linarith)
    · exact h1 (by linarith)
  have hstep : ∀ x : S, x.1.num.natAbs + x.1.den + 1 ≤ ((f x : S):ℚ).num.natAbs + ((f x : S):ℚ).den := by
    intro x
    have hfx : ((f x : S):ℚ) = (x:ℚ) - 1/(x:ℚ) := by rw [hf]
    rw [hfx]
    obtain ⟨h0, h2⟩ := hS' x
    have hq : (0:ℤ) < ((x.1.den:ℕ):ℤ) := by exact_mod_cast x.1.den_pos
    have hxe : (x:ℚ) = (x.1.num:ℚ)/(((x.1.den:ℕ):ℤ):ℚ) := by
      rw [Int.cast_natCast, Rat.num_div_den]
    have hc : IsCoprime x.1.num ((x.1.den:ℕ):ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.1.reduced
    have hp : x.1.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have := key_pq (x:ℚ) x.1.num ((x.1.den:ℕ):ℤ) hq hxe hc hp h2
    have e : ((x.1.den:ℕ):ℤ).natAbs = x.1.den := rfl
    rw [e] at this
    exact this
  have hiter : ∀ n : ℕ, ∀ x : S, x.1.num.natAbs + x.1.den + n ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      have h1 := ih (f x)
      have h2 := hstep x
      omega
  refine iff_of_true ?_ trivial
  ext y; simp only [mem_empty_iff_false, iff_false]
  intro hy
  simp only [mem_iInter, mem_image, mem_univ, true_and, mem_Ici] at hy
  obtain ⟨x, hx⟩ := hy (y.1.num.natAbs + y.1.den + 1) (by omega)
  have := hiter (y.1.num.natAbs + y.1.den + 1) x
  rw [hx] at this
  omega
