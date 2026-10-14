import Mathlib
lemma key0 (x : ℚ) (h0 : 0 < x) (h1 : x ≠ 1) :
    x.num.natAbs + x.den < (x - 1/x).num.natAbs + (x - 1/x).den := by
  have hq : 0 < x.den := x.den_pos
  have hp : 0 < x.num := Rat.num_pos.mpr h0
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact x.reduced
  have hxe : x = (x.num : ℚ) / (x.den : ℤ) := by simp [Rat.num_div_den]
  have hne1 : ¬ (x.num = 1 ∧ (x.den:ℤ) = 1) := by
    rintro ⟨a, b⟩
    apply h1; rw [hxe, a, b]; simp
  have hpa : (x.num.natAbs : ℤ) = x.num := Int.natAbs_of_nonneg hp.le
  generalize x.num = p at *
  generalize hqd : (x.den : ℤ) = q at *
  have hqpos : 0 < q := by omega
  have hqne : (q:ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hpne : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hy : x - 1/x = (((p^2-q^2) : ℤ) : ℚ) / ((p * q : ℤ) : ℚ) := by
    rw [hxe]; push_cast
    field_simp
  have c1 : IsCoprime (p^2-q^2) (p*q) := by
    apply IsCoprime.mul_right
    · have : IsCoprime (-(q^2)) p := (hcop.symm.pow_left).neg_left
      have h := this.add_mul_left_left p
      have e : p^2-q^2 = -(q^2)+p*p := by ring
      rw [e]; exact h
    · have : IsCoprime (p^2) q := hcop.pow_left
      have h := this.add_mul_left_left (-q)
      have e : p^2-q^2 = p^2+q*(-q) := by ring
      rw [e]; exact h
  have hc : Nat.Coprime (p^2-q^2).natAbs (p*q).natAbs :=
    Int.isCoprime_iff_gcd_eq_one.mp c1
  have hbpos : 0 < p*q := by positivity
  have hnum := Rat.num_div_eq_of_coprime hbpos hc
  have hden := Rat.den_div_eq_of_coprime hbpos hc
  have hN : |(x-1/x).num| = |p^2-q^2| := by
    rw [hy, hnum]
  have hD : (((x-1/x).den : ℕ) : ℤ) = p*q := by rw [hy]; exact hden
  zify
  rw [hN, hD, hqd]
  have : p ≠ q ∨ (p = 1 ∧ q = 1) := by
    by_cases h : p = q
    · right
      subst h
      have : IsUnit p := isCoprime_self.mp hcop
      have : p = 1 := by rcases Int.isUnit_iff.mp this with h | h <;> omega
      exact ⟨this, this⟩
    · left; exact h
  rcases this with h | ⟨a, b⟩
  · rw [abs_of_pos hp]
    rcases lt_or_gt_of_ne h with h | h
    · rw [abs_of_neg (by nlinarith)]; nlinarith
    · rw [abs_of_pos (by nlinarith)]; nlinarith
  · exact absurd ⟨a, by omega⟩ hne1

open Topology Filter Polynomial Set

noncomputable abbrev putnam_2001_b4_solution : Prop := True
theorem putnam_2001_b4
(S : Set ℚ)
(hS : S = univ \ {-1, 0, 1})
(f : S → S)
(hf : ∀ x : S, f x = x - 1 / (x : ℚ))
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution := by
  have key : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den < (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x a b c
    rcases lt_or_gt_of_ne a with h | h
    · have := key0 (-x) (by linarith) (by intro e; apply c; linarith)
      have e : -x - 1 / -x = -(x - 1/x) := by ring
      rw [e] at this
      simp only [Rat.neg_num, Rat.neg_den, Int.natAbs_neg] at this
      exact this
    · exact key0 x h b
  have mem : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ) ≠ 1 ∧ (x:ℚ) ≠ -1 := by
    intro ⟨x, hx⟩
    subst hS
    simp at hx
    exact ⟨hx.2.1, hx.2.2, hx.1⟩
  have step : ∀ x : S, (x:ℚ).num.natAbs + (x:ℚ).den < ((f x : S):ℚ).num.natAbs + ((f x : S):ℚ).den := by
    intro x
    rw [hf x]
    obtain ⟨a, b, c⟩ := mem x
    exact key _ a b c
  have grow : ∀ n : ℕ, ∀ x : S, n ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      have := step (f^[n] x)
      have := ih x
      omega
  have : ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro z hz
    simp only [Set.mem_iInter] at hz
    obtain ⟨x, -, hx⟩ := hz (((z:ℚ).num.natAbs + (z:ℚ).den) + 1) (by simp [Set.mem_Ici])
    have := grow (((z:ℚ).num.natAbs + (z:ℚ).den) + 1) x
    rw [hx] at this
    omega
  rw [this]; simp [putnam_2001_b4_solution]
