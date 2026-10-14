import Mathlib
open Topology Filter Polynomial Set
noncomputable abbrev putnam_2001_b4_solution : Prop := True
lemma ineq (a q : ℤ) (ha : 1 ≤ a) (hq : 1 ≤ q) (h : a ≠ q) :
    a + q + 1 ≤ |a^2 - q^2| + a * q := by
  rcases lt_or_gt_of_ne h with h' | h'
  · have : a^2 - q^2 = -((q-a)*(q+a)) := by ring
    have h3 : |a^2-q^2| = (q-a)*(q+a) := by
      rw [this, abs_neg, abs_of_nonneg (by nlinarith)]
    rw [h3]; nlinarith
  · have h3 : |a^2-q^2| = (a-q)*(a+q) := by
      rw [abs_of_nonneg (by nlinarith)]; ring
    rw [h3]; nlinarith

lemma key (x : ℚ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    (x.num.natAbs + x.den) + 1 ≤ ((x - 1/x).num.natAbs + (x - 1/x).den) := by
  have hq : (0:ℤ) < (x.den:ℤ) := by exact_mod_cast x.pos
  have hxe : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hcop : IsCoprime x.num (x.den:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
  have hp0 : x.num ≠ 0 := by
    intro h; apply h0; rw [hxe, h]; simp
  have hdQ : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hpq1 : x.num ≠ (x.den:ℤ) := by
    intro h
    apply h1
    rw [hxe]
    have : ((x.num:ℤ):ℚ) = ((x.den:ℤ):ℚ) := by rw [h]
    rw [this]; push_cast; field_simp
  have hpq2 : x.num ≠ -(x.den:ℤ) := by
    intro h
    apply h2
    rw [hxe]
    have : ((x.num:ℤ):ℚ) = -((x.den:ℤ):ℚ) := by rw [h]; push_cast; ring
    rw [this]; push_cast; field_simp
  set p := x.num with hp
  set q : ℤ := (x.den:ℤ) with hqdef
  have hcopA : IsCoprime (p^2 - q^2) (p*q) := by
    have hq2 : IsCoprime (-(q^2)) p := by
      have := hcop.symm.pow_left (m := 2)
      exact (this.neg_left)
    have hp' : IsCoprime (p^2 - q^2) p := by
      have := hq2.add_mul_left_left p
      have e : p^2 - q^2 = -(q^2) + p*p := by ring
      rw [e]; exact this
    have hq' : IsCoprime (p^2 - q^2) q := by
      have := (hcop.pow_left (m := 2)).add_mul_left_left (-q)
      have e : p^2 - q^2 = p^2 + q*(-q) := by ring
      rw [e]; exact this
    exact hp'.mul_right hq'
  have hxQ : x = (p:ℚ)/(q:ℚ) := hxe
  have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast hp0
  have hqQ : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hxval : x - 1/x = ((p^2 - q^2 : ℤ):ℚ) / ((p*q : ℤ):ℚ) := by
    rw [hxQ]
    push_cast
    field_simp
  have hq1 : (1:ℤ) ≤ q := by omega
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · have hB : (0:ℤ) < -(p*q) := by nlinarith
    have hcopN : Nat.Coprime (-(p^2 - q^2)).natAbs (-(p*q)).natAbs :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopA.neg_left.neg_right
    have hyv : x - 1/x = ((-(p^2 - q^2) : ℤ):ℚ) / ((-(p*q) : ℤ):ℚ) := by
      rw [hxval]; push_cast; rw [neg_div_neg_eq]
    have hnum := Rat.num_div_eq_of_coprime hB hcopN
    have hden := Rat.den_div_eq_of_coprime hB hcopN
    rw [hyv, hnum]
    have hi := ineq (-p) q (by omega) hq1 (by omega)
    have hab : |p| = -p := abs_of_neg hneg
    have hA : |(-p)^2 - q^2| = |p^2 - q^2| := by ring_nf
    rw [hA] at hi
    have hd : (((-(p^2 - q^2) : ℤ):ℚ) / ((-(p*q) : ℤ):ℚ)).den = (-(p*q)).toNat := by
      omega
    rw [hd]
    have ht : ((-(p*q)).toNat : ℤ) = -(p*q) := Int.toNat_of_nonneg hB.le
    have e1 : ((x.num.natAbs + x.den + 1 : ℕ) : ℤ) ≤ (((-(p^2 - q^2)).natAbs + (-(p*q)).toNat : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_one, Int.natCast_natAbs, ht, abs_neg]
      rw [← hp, hab]
      nlinarith [hi]
    exact_mod_cast e1
  · have hB : (0:ℤ) < p*q := by nlinarith
    have hcopN : Nat.Coprime (p^2 - q^2).natAbs (p*q).natAbs :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopA
    rw [hxval, Rat.num_div_eq_of_coprime hB hcopN]
    have hi := ineq p q (by omega) hq1 hpq1
    have hden := Rat.den_div_eq_of_coprime hB hcopN
    have hd : (((p^2 - q^2 : ℤ):ℚ) / ((p*q : ℤ):ℚ)).den = (p*q).toNat := by
      omega
    rw [hd]
    have ht : ((p*q).toNat : ℤ) = p*q := Int.toNat_of_nonneg hB.le
    have e1 : ((x.num.natAbs + x.den + 1 : ℕ) : ℤ) ≤ (((p^2 - q^2).natAbs + (p*q).toNat : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_one, Int.natCast_natAbs, ht]
      rw [← hp, abs_of_pos hpos]
      nlinarith [hi]
    exact_mod_cast e1

theorem putnam_2001_b4
(S : Set ℚ)
(hS : S = univ \ {-1, 0, 1})
(f : S → S)
(hf : ∀ x : S, f x = x - 1 / (x : ℚ))
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution := by
  have hS' : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ) ≠ 1 ∧ (x:ℚ) ≠ -1 := by
    intro x
    have := x.2
    have h2 : (x:ℚ) ∈ univ \ {-1, 0, 1} := hS ▸ this
    simp only [Set.mem_sdiff, mem_univ, mem_insert_iff, mem_singleton_iff, true_and, not_or] at h2
    exact ⟨h2.2.1, h2.2.2, h2.1⟩
  have hH : ∀ n : ℕ, ∀ z : S, ((z:ℚ).num.natAbs + (z:ℚ).den) + n ≤
      (((f^[n] z : S) : ℚ).num.natAbs + ((f^[n] z : S) : ℚ).den) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply']
      have h1 := ih z
      obtain ⟨a, b, c⟩ := hS' (f^[n] z)
      have hfx : ((f (f^[n] z) : S) : ℚ) = ((f^[n] z : S) : ℚ) - 1 / ((f^[n] z : S) : ℚ) := by
        rw [hf]
      rw [hfx]
      have := key _ a b c
      omega
  refine iff_of_true ?_ trivial
  rw [eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_iInter₂] at hy
  obtain ⟨z, -, hz⟩ := hy ((((y:ℚ)).num.natAbs + (y:ℚ).den) + 1) (by simp)
  have := hH (((y:ℚ)).num.natAbs + (y:ℚ).den + 1) z
  rw [hz] at this
  omega
