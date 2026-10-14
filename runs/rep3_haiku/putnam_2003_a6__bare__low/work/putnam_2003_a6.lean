import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True

/-- Thue–Morse signs: tm (2k) = tm k, tm (2k+1) = - tm k. -/
def tm (n : ℕ) : ℤ := if n = 0 then 1 else if n % 2 = 0 then tm (n / 2) else - tm (n / 2)
termination_by n
decreasing_by all_goals omega

lemma tm_even (k : ℕ) : tm (2*k) = tm k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [tm]
    simp [show 2*k ≠ 0 by omega, show 2*k % 2 = 0 by omega, show 2*k/2 = k by omega]

lemma tm_odd (k : ℕ) : tm (2*k+1) = - tm k := by
  rw [tm]
  simp [show (2*k+1) % 2 = 1 by omega, show (2*k+1)/2 = k by omega]

lemma tm_pm (n : ℕ) : tm n = 1 ∨ tm n = -1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · left; simp [tm]
      · rw [tm_even]; exact ih k (by omega)
    · rw [tm_odd]; rcases ih k (by omega) with h | h <;> simp [h]

lemma tm_sum_even (j : ℕ) : ∑ a ∈ Finset.range (2*j), tm a = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2*(j+1) = 2*j+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      tm_odd, tm_even]
    ring

lemma key_sum (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a + b = n ∧ a ≠ b then tm a + tm b else 0) = 0 := by
  have split : ∀ a b : ℕ, (if a + b = n ∧ a ≠ b then tm a + tm b else 0)
      = (if a + b = n ∧ a ≠ b then tm a else 0) + (if a + b = n ∧ a ≠ b then tm b else 0) := by
    intro a b; split_ifs <;> ring
  have comm : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a + b = n ∧ a ≠ b then tm b else 0)
      = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a + b = n ∧ a ≠ b then tm a else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : a + b = n <;> by_cases h' : a = b <;> simp [h, h', add_comm, eq_comm]
  simp only [split, Finset.sum_add_distrib, comm]
  suffices h : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a + b = n ∧ a ≠ b then tm a else 0) = 0 by
    rw [h, add_zero]
  have inner : ∀ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      (if a + b = n ∧ a ≠ b then tm a else 0) = (if 2*a ≠ n then tm a else 0) := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.sum_eq_single (n - a)]
    · by_cases h : 2*a = n
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_pos (by omega), if_pos (by omega)]
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro h; exfalso; apply h; rw [Finset.mem_range]; omega
  rw [Finset.sum_congr rfl inner]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h : ∀ a ∈ Finset.range (2*m+1), (if 2*a ≠ 2*m then tm a else 0)
        = tm a - (if a = m then tm m else 0) := by
      intro a _
      by_cases h : a = m
      · subst h; simp
      · rw [if_pos (by omega), if_neg h]; simp
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    rw [Finset.sum_range_succ, tm_sum_even, tm_even]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    ring
  · have h : ∀ a ∈ Finset.range (2*m+1+1), (if 2*a ≠ 2*m+1 then tm a else 0) = tm a := by
      intro a _; rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl h, show 2*m+1+1 = 2*(m+1) by ring, tm_sum_even]

open scoped Classical in
noncomputable def indf (S : Set ℕ) (n a b : ℕ) : ℕ :=
  if (a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a + b = n) then 1 else 0

lemma r_eq (S : Set ℕ) (n : ℕ) :
    (∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
      = ∑' a : ℕ, ∑' b : ℕ, indf S n a b := by
  have h1 : ∀ s1 : S, (∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
      = ∑' b : ℕ, S.indicator (fun b => if (s1.1 ≠ b ∧ s1.1 + b = n) then 1 else 0) b := by
    intro s1
    rw [← tsum_subtype S (fun b => if (s1.1 ≠ b ∧ s1.1 + b = n) then 1 else 0)]
    congr 1; funext s2
    simp [Subtype.ext_iff]
  simp_rw [h1]
  refine Eq.trans (tsum_subtype S (fun a : ℕ => ∑' b : ℕ,
    S.indicator (fun b => if (a ≠ b ∧ a + b = n) then 1 else 0) b)) ?_
  congr 1; funext a
  by_cases ha : a ∈ S
  · rw [Set.indicator_of_mem ha]
    congr 1; funext b
    simp only [Set.indicator_apply, indf]
    by_cases hb : b ∈ S <;> by_cases hab : a ≠ b <;> by_cases hs : a + b = n <;>
      simp [ha, hb, hab, hs]
  · rw [Set.indicator_of_notMem ha]
    simp only [indf]
    simp [ha]

lemma fin_eq (S : Set ℕ) (n : ℕ) :
    ∑' a : ℕ, ∑' b : ℕ, indf S n a b
      = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), indf S n a b := by
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    intro b hb
    rw [Finset.mem_range] at hb
    simp only [indf]
    rw [if_neg]
    rintro ⟨_, _, _, h⟩
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    have : ∀ b, indf S n a b = 0 := by
      intro b; simp only [indf]; rw [if_neg]
      rintro ⟨_, _, _, h⟩; omega
    simp [this]
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution :=
by
  constructor
  · intro _; trivial
  · intro _
    refine ⟨{x | tm x = 1}, {x | tm x = -1}, ?_, ?_, ?_⟩
    · ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases tm_pm x with h | h <;> simp [h]
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩
      rw [h1] at h2; norm_num at h2
    · intro n
      rw [hr, hr, r_eq, r_eq, fin_eq, fin_eq]
      have hpt : ∀ a b : ℕ, 2 * (((indf {x | tm x = 1} n a b : ℕ) : ℤ)
          - ((indf {x | tm x = -1} n a b : ℕ) : ℤ))
          = (if a + b = n ∧ a ≠ b then tm a + tm b else 0) := by
        intro a b
        have ha := tm_pm a
        have hb := tm_pm b
        unfold indf
        by_cases h : a + b = n <;> by_cases h' : a = b <;>
          rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          simp [h, h', ha, hb] <;> omega
      have h2 : (2:ℤ) * ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
          (((indf {x | tm x = 1} n a b : ℕ) : ℤ) - ((indf {x | tm x = -1} n a b : ℕ) : ℤ)) = 0 := by
        simp only [Finset.mul_sum]
        rw [← key_sum n]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        exact hpt a b
      have hD : ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
          (((indf {x | tm x = 1} n a b : ℕ) : ℤ) - ((indf {x | tm x = -1} n a b : ℕ) : ℤ)) = 0 := by
        linarith
      simp only [Finset.sum_sub_distrib] at hD
      have : ((∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), indf {x | tm x = 1} n a b : ℕ) : ℤ)
          = ((∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), indf {x | tm x = -1} n a b : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast this
