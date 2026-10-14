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
  have hdiv0 : ∀ a b : ℤ, 0 < b → IsCoprime a b →
      ((a:ℚ)/b).num.natAbs + ((a:ℚ)/b).den = a.natAbs + b.natAbs := by
    intro a b hb h
    have hc : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
    have h1 := Rat.num_div_eq_of_coprime hb hc
    have h2 := Rat.den_div_eq_of_coprime hb hc
    have h3 : ((a:ℚ)/b).den = b.natAbs := by omega
    rw [h1, h3]
  have hdiv : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b →
      ((a:ℚ)/b).num.natAbs + ((a:ℚ)/b).den = a.natAbs + b.natAbs := by
    intro a b hb0 h
    rcases lt_or_gt_of_ne hb0 with hneg | hpos
    · have e : (a:ℚ)/b = ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := by
        push_cast; rw [neg_div_neg_eq]
      rw [e]
      have := hdiv0 (-a) (-b) (by omega) (h.neg_left.neg_right)
      simpa [Int.natAbs_neg] using this
    · exact hdiv0 a b hpos h
  have alg : ∀ (p : ℤ) (q : ℕ), (q:ℤ) ≠ 0 → p ≠ 0 →
      (p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ)) = ((p^2-(q:ℤ)^2 : ℤ):ℚ)/((p*(q:ℤ) : ℤ):ℚ) := by
    intro p q hq hp
    have hq' : (q:ℚ) ≠ 0 := by exact_mod_cast hq
    have hp' : (p:ℚ) ≠ 0 := by exact_mod_cast hp
    push_cast
    field_simp
  have key : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → x ≠ -1 →
      x.num.natAbs + x.den + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
    intro x h0 h1 hm1
    have hp : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hq : ((x.den:ℕ):ℤ) ≠ 0 := by exact_mod_cast x.den_nz
    have hxe := alg x.num x.den hq hp
    rw [Rat.num_div_den] at hxe
    rw [hxe]
    have hcop : IsCoprime x.num (x.den:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
    have c1 : IsCoprime (x.num^2 - ((x.den:ℕ):ℤ)^2) x.num := by
      have h := (hcop.symm.pow_left (m := 2)).neg_left
      have e : x.num^2 - ((x.den:ℕ):ℤ)^2 = -(((x.den:ℕ):ℤ)^2) + x.num * x.num := by ring
      rw [e]
      exact h.add_mul_left_left x.num
    have c2 : IsCoprime (x.num^2 - ((x.den:ℕ):ℤ)^2) ((x.den:ℕ):ℤ) := by
      have h := (hcop.pow_left (m := 2))
      have e : x.num^2 - ((x.den:ℕ):ℤ)^2 = x.num^2 + ((x.den:ℕ):ℤ) * (-((x.den:ℕ):ℤ)) := by ring
      rw [e]
      exact h.add_mul_left_left (-((x.den:ℕ):ℤ))
    have hc := IsCoprime.mul_right c1 c2
    have hb : x.num * ((x.den:ℕ):ℤ) ≠ 0 := mul_ne_zero hp hq
    rw [hdiv _ _ hb hc]
    have hne : x.num.natAbs ≠ x.den := by
      intro heq
      have hx : x = (x.num:ℚ)/(x.den:ℚ) := (Rat.num_div_den x).symm
      have hd : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
      rcases Int.natAbs_eq x.num with h | h
      · apply h1
        rw [hx, h, heq]
        push_cast
        rw [div_self hd]
      · apply hm1
        rw [hx, h, heq]
        push_cast
        rw [neg_div, div_self hd]
    have hpos : 0 < x.num.natAbs := Int.natAbs_pos.mpr hp
    have hqpos : 0 < x.den := x.den_pos
    have hN : x.num^2 = ((x.num.natAbs : ℕ):ℤ)^2 := (Int.natAbs_sq _).symm
    have hna : (((x.den:ℕ):ℤ)).natAbs = x.den := by simp
    rw [hN, Int.natAbs_mul, hna]
    generalize x.num.natAbs = a at *
    generalize x.den = b at *
    have hA : (1:ℤ) ≤ a := by exact_mod_cast hpos
    have hB : (1:ℤ) ≤ b := by exact_mod_cast hqpos
    have hab : (a:ℤ) ≠ b := by exact_mod_cast hne
    have hmain : (a:ℤ) + b + 1 ≤ |(a:ℤ)^2 - (b:ℤ)^2| + a*b := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · rcases abs_cases ((a:ℤ)^2 - (b:ℤ)^2) with ⟨h2, _⟩ | ⟨h2, _⟩
        · nlinarith
        · nlinarith
      · rcases abs_cases ((a:ℤ)^2 - (b:ℤ)^2) with ⟨h2, _⟩ | ⟨h2, _⟩
        · nlinarith
        · nlinarith
    have := hmain
    rw [← Int.natCast_natAbs] at this
    zify
    linarith
  have hS' : ∀ z : S, (z:ℚ) ≠ 0 ∧ (z:ℚ) ≠ 1 ∧ (z:ℚ) ≠ -1 := by
    intro z
    have hz : (z:ℚ) ∈ univ \ {-1, 0, 1} := by rw [← hS]; exact z.2
    simp only [Set.mem_sdiff, mem_univ, mem_insert_iff, mem_singleton_iff, true_and, not_or] at hz
    exact ⟨hz.2.1, hz.2.2, hz.1⟩
  have hstep : ∀ z : S, (z:ℚ).num.natAbs + (z:ℚ).den + 1 ≤ ((f z : S):ℚ).num.natAbs + ((f z : S):ℚ).den := by
    intro z
    obtain ⟨h0, h1, hm1⟩ := hS' z
    rw [hf z]
    exact key z h0 h1 hm1
  have hiter : ∀ m : ℕ, ∀ z : S, (z:ℚ).num.natAbs + (z:ℚ).den + m ≤ ((f^[m] z : S):ℚ).num.natAbs + ((f^[m] z : S):ℚ).den := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply']
      have := hstep (f^[k] z)
      have := ih z
      omega
  have hpos : ∀ q : ℚ, 1 ≤ q.num.natAbs + q.den := fun q => by
    have := q.den_pos
    omega
  simp only [putnam_2001_b4_solution, iff_true]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨x, _, hx⟩ := mem_iInter₂.mp hy _ (mem_Ici.mpr (hpos (y:ℚ)))
  have h := hiter ((y:ℚ).num.natAbs + (y:ℚ).den) x
  rw [hx] at h
  have := hpos (x:ℚ)
  omega
