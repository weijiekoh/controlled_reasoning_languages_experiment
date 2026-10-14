import Mathlib

open Topology Filter

noncomputable abbrev putnam_2019_a5_solution : ℕ → ℕ := (fun p : ℕ => (p - 1) / 2)
/--
Let $p$ be an odd prime number, and let $\mathbb{F}_p$ denote the field of integers modulo $p$. Let $\mathbb{F}_p[x]$ be the ring of polynomials over $\mathbb{F}_p$, and let $q(x) \in \mathbb{F}_p[x]$ be given by $q(x)=\sum_{k=1}^{p-1} a_kx^k$, where $a_k=k^{(p-1)/2}\mod{p}$. Find the greatest nonnegative integer $n$ such that $(x-1)^n$ divides $q(x)$ in $\mathbb{F}_p[x]$.
-/
theorem putnam_2019_a5
  (p : ℕ)
  (q : Polynomial (ZMod p))
  (a : ℕ → ZMod p)
  (npoly : ℕ → Polynomial (ZMod p))
  (podd : Odd p)
  (pprime : p.Prime)
  (hq : ∀ k : ℕ, q.coeff k = a k)
  (ha0 : a 0 = 0 ∧ ∀ k > p - 1, a k = 0)
  (haother : ∀ k : Set.Icc 1 (p - 1), a k = ((k : ℕ) ^ ((p - 1) / 2)) % p)
  (hnpoly : ∀ n : ℕ, npoly n = (Polynomial.X - 1) ^ n) :
  IsGreatest {n | npoly n ∣ q} (putnam_2019_a5_solution p) := by
  have := Fact.mk pprime
  have hp2 := pprime.two_le
  obtain ⟨r, hr⟩ := podd
  set m := (p - 1) / 2 with hm
  have hpm : p = 2 * m + 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hqk : ∀ k < p, q.coeff k = (k : ZMod p) ^ m := by
    intro k hk
    rw [hq k]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [ha0.1]
      simp [zero_pow (by omega : m ≠ 0)]
    · have h := haother ⟨k, Set.mem_Icc.mpr ⟨hpos, by omega⟩⟩
      simp only at h
      rw [h, ZMod.natCast_mod, Nat.cast_pow]
  have hqz : ∀ x, p ≤ x → q.coeff x = 0 := by
    intro x hx
    rw [hq x, ha0.2 x (by omega)]
  have hdeg : q.natDegree ≤ p - 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => hqz N (by omega))
  -- coefficients of the Taylor shift
  have hcoeff : ∀ j, (Polynomial.taylor 1 q).coeff j
      = ∑ k ∈ Finset.range p, ((k.choose j : ℕ) : ZMod p) * q.coeff k := by
    intro j
    rw [Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range' (n := p + j)
      (by have := Polynomial.natDegree_hasseDeriv_le q j; omega)]
    simp only [one_pow, mul_one, Polynomial.hasseDeriv_coeff]
    set g : ℕ → ZMod p := fun k => ((k.choose j : ℕ) : ZMod p) * q.coeff k with hg
    have hgz : ∀ x, p ≤ x → g x = 0 := by
      intro x hx; simp only [hg, hqz x hx, mul_zero]
    have hgj : ∀ x < j, g x = 0 := by
      intro x hx; simp only [hg, Nat.choose_eq_zero_of_lt hx, Nat.cast_zero, zero_mul]
    have h1 := Finset.sum_range_add g p j
    have h2 := Finset.sum_range_add g j p
    rw [add_comm j p] at h2
    have z1 : ∑ x ∈ Finset.range j, g (p + x) = 0 :=
      Finset.sum_eq_zero (fun x _ => hgz _ (by omega))
    have z2 : ∑ x ∈ Finset.range j, g x = 0 :=
      Finset.sum_eq_zero (fun x hx => hgj x (Finset.mem_range.mp hx))
    have hA : ∑ x ∈ Finset.range p, g (x + j) = ∑ k ∈ Finset.range p, g k := by
      rw [z1, add_zero] at h1
      rw [z2, zero_add] at h2
      rw [h2] at h1
      exact (Finset.sum_congr rfl (fun x _ => by rw [add_comm])).trans h1
    have h3 := Finset.sum_range_add (fun i => g (i + j)) p j
    rw [h3]
    have z3 : ∑ x ∈ Finset.range j, g (p + x + j) = 0 :=
      Finset.sum_eq_zero (fun x _ => hgz _ (by omega))
    rw [z3, add_zero]
    exact hA
  have hconv : ∀ f : ZMod p → ZMod p, ∑ k ∈ Finset.range p, f (k : ZMod p) = ∑ x, f x := by
    intro f
    have himg : Finset.image (Nat.cast : ℕ → ZMod p) (Finset.range p) = Finset.univ := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
      obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective x
      exact ⟨k % p, Nat.mod_lt _ (by omega), ZMod.natCast_mod k p⟩
    rw [← himg, Finset.sum_image]
    intro a ha b hb hab
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp ha), Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at this
  have hS : ∀ i < p, ∑ k ∈ Finset.range p, (k : ZMod p) ^ i = if i = p - 1 then -1 else 0 := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      rw [if_neg (by omega)]
      simp
    · by_cases hpi : i = p - 1
      · rw [if_pos hpi, hpi]
        rw [show Finset.range p = Finset.range ((p-1)+1) from by congr 1; omega,
          Finset.sum_range_succ']
        have hne : ∀ k ∈ Finset.range (p-1), ((k+1 : ℕ) : ZMod p) ^ (p-1) = 1 := by
          intro k hk
          apply ZMod.pow_card_sub_one_eq_one
          intro h
          have h := (ZMod.natCast_eq_zero_iff _ _).mp h
          have := Nat.le_of_dvd (by omega) h
          have := Finset.mem_range.mp hk
          omega
        rw [Finset.sum_congr rfl hne, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, Nat.cast_zero, zero_pow (by omega), add_zero,
          Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self]
        simp
      · rw [if_neg hpi]
        have := hconv (fun x => x ^ i)
        rw [this]
        exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by rw [ZMod.card]; omega)
  have hsum : ∀ G : Polynomial (ZMod p), G.natDegree < p →
      ∑ k ∈ Finset.range p, G.eval (k : ZMod p) = -G.coeff (p-1) := by
    intro G hG
    calc ∑ k ∈ Finset.range p, G.eval (k : ZMod p)
        = ∑ k ∈ Finset.range p, ∑ i ∈ Finset.range p, G.coeff i * (k : ZMod p) ^ i :=
          Finset.sum_congr rfl (fun k _ => Polynomial.eval_eq_sum_range' hG _)
      _ = ∑ i ∈ Finset.range p, G.coeff i * ∑ k ∈ Finset.range p, (k : ZMod p) ^ i := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range p, G.coeff i * (if i = p - 1 then -1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hS i (Finset.mem_range.mp hi)]
      _ = -G.coeff (p-1) := by
          rw [Finset.sum_eq_single (p-1)]
          · simp
          · intro i _ hi; rw [if_neg hi, mul_zero]
          · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hdesc : ∀ j ≤ m, ((j.factorial : ℕ) : ZMod p) *
      ∑ k ∈ Finset.range p, ((k.choose j : ℕ) : ZMod p) * (k : ZMod p) ^ m
      = -((descPochhammer (ZMod p) j * Polynomial.X ^ m).coeff (p-1)) := by
    intro j hj
    have hdeg2 : (descPochhammer (ZMod p) j * Polynomial.X ^ m).natDegree < p := by
      have h1 := Polynomial.natDegree_mul_le (p := descPochhammer (ZMod p) j)
        (q := Polynomial.X ^ m)
      have h2 := descPochhammer_natDegree (ZMod p) j
      simp only [Polynomial.natDegree_X_pow] at h1
      omega
    rw [Finset.mul_sum, ← hsum _ hdeg2]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hTj : ∀ j, (Polynomial.taylor 1 q).coeff j
      = ∑ k ∈ Finset.range p, ((k.choose j : ℕ) : ZMod p) * (k : ZMod p) ^ m := by
    intro j
    rw [hcoeff j]
    exact Finset.sum_congr rfl (fun k hk => by rw [hqk k (Finset.mem_range.mp hk)])
  have hcoefD : ∀ j ≤ m, (descPochhammer (ZMod p) j * Polynomial.X ^ m).coeff (p-1)
      = (descPochhammer (ZMod p) j).coeff m := by
    intro j _
    rw [show p - 1 = m + m by omega, Polynomial.coeff_mul_X_pow]
  have hfact : ∀ j < p, ((j.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro j hj h
    have h := (ZMod.natCast_eq_zero_iff _ _).mp h
    have := (Nat.Prime.dvd_factorial pprime).mp h
    omega
  have key1 : ∀ j < m, (Polynomial.taylor 1 q).coeff j = 0 := by
    intro j hj
    have h := hdesc j hj.le
    rw [hcoefD j hj.le, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [descPochhammer_natDegree]; exact hj), neg_zero] at h
    rw [hTj j]
    exact (mul_eq_zero.mp h).resolve_left (hfact j (by omega))
  have key2 : (Polynomial.taylor 1 q).coeff m ≠ 0 := by
    intro h
    rw [hTj m] at h
    have h2 := hdesc m le_rfl
    rw [hcoefD m le_rfl, h, mul_zero] at h2
    have hmon := (monic_descPochhammer (ZMod p) m).coeff_natDegree
    rw [descPochhammer_natDegree] at hmon
    rw [hmon] at h2
    exact one_ne_zero (neg_eq_zero.mp h2.symm)
  have key : ∀ n, (Polynomial.X - 1) ^ n ∣ q ↔
      ∀ d < n, (Polynomial.taylor 1 q).coeff d = 0 := by
    intro n
    rw [← Polynomial.X_pow_dvd_iff]
    have hX1 : Polynomial.taylor (1 : ZMod p) (Polynomial.X - 1) = Polynomial.X := by
      have h1 : (1 : Polynomial (ZMod p)) = Polynomial.C 1 := (map_one _).symm
      rw [map_sub, Polynomial.taylor_X, h1, Polynomial.taylor_C]
      simp
    have hX2 : Polynomial.taylor (-1 : ZMod p) Polynomial.X = Polynomial.X - 1 := by
      rw [Polynomial.taylor_X]
      simp [sub_eq_add_neg]
    have hback : ∀ s, Polynomial.taylor (-1 : ZMod p) (Polynomial.taylor 1 s) = s := by
      intro s
      rw [Polynomial.taylor_taylor, show (-1 : ZMod p) + 1 = 0 by ring, Polynomial.taylor_zero]
    constructor
    · intro h
      obtain ⟨s, hs⟩ := h
      exact ⟨Polynomial.taylor 1 s, by
        rw [hs, Polynomial.taylor_mul, Polynomial.taylor_pow, hX1]⟩
    · rintro ⟨s, hs⟩
      refine ⟨Polynomial.taylor (-1) s, ?_⟩
      calc q = Polynomial.taylor (-1) (Polynomial.taylor 1 q) := (hback q).symm
        _ = Polynomial.taylor (-1) (Polynomial.X ^ n * s) := by rw [hs]
        _ = _ := by rw [Polynomial.taylor_mul, Polynomial.taylor_pow, hX2]
  constructor
  · show npoly m ∣ q
    rw [hnpoly, key]
    intro d hd
    exact key1 d hd
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly, key] at hn'
    show n ≤ m
    by_contra hlt
    exact key2 (hn' m (by omega))
