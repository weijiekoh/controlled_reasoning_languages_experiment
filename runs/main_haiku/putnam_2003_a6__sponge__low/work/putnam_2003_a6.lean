import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
/--
For a set $S$ of nonnegative integers, let $r_S(n)$ denote the number of ordered pairs $(s_1,s_2)$ such that $s_1 \in S$, $s_2 \in S$, $s_1 \ne s_2$, and $s_1+s_2=n$. Is it possible to partition the nonnegative integers into two sets $A$ and $B$ in such a way that $r_A(n)=r_B(n)$ for all $n$?
-/
theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℕ, ∀ n, s n = (Nat.digits 2 n).sum := ⟨_, fun _ => rfl⟩
  have hs0 : ∀ m, s (2 * m) = s m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hs]
    · have h := Nat.digits_add 2 (by norm_num) 0 m (by norm_num) (Or.inr hm.ne')
      rw [hs, hs, show 2 * m = 0 + 2 * m by ring, h]
      simp
  have hs1 : ∀ m, s (2 * m + 1) = s m + 1 := by
    intro m
    have h := Nat.digits_add 2 (by norm_num) 1 m (by norm_num) (Or.inl one_ne_zero)
    rw [hs, hs, show 2 * m + 1 = 1 + 2 * m by ring, h, List.sum_cons]
    ring
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, ∀ x, e x = if Even (s x) then 1 else -1 := ⟨_, fun _ => rfl⟩
  have he0 : ∀ m, e (2 * m) = e m := by
    intro m
    simp only [he, hs0]
  have he1 : ∀ m, e (2 * m + 1) = - e m := by
    intro m
    simp only [he, hs1]
    by_cases h : Even (s m) <;> simp [h, Nat.even_add_one]
  have hP : ∀ m, ∑ x ∈ Finset.range (2 * m + 1), e x = e m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, he1 k, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, he0]
      ring
  have hPodd : ∀ m, ∑ x ∈ Finset.range (2 * m + 1 + 1), e x = 0 := by
    intro m
    rw [Finset.sum_range_succ, hP m, he1 m]
    ring
  have key1 : ∀ (P : ℕ → Prop) [DecidablePred P] (n x : ℕ) (f : ℕ → ℕ → ℕ),
      (∀ a b, f a b ≠ 0 → a ≤ n ∧ b ≤ n) →
      ∑' s2 : {y | P y}, f x s2 = ∑ y ∈ Finset.range (n + 1), if P y then f x y else 0 := by
    intro P _ n x f hf
    rw [tsum_subtype {y | P y} (f x)]
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hyP : P y <;> simp [Set.indicator_apply, hyP]
    · intro y hy
      by_cases hyP : P y
      · rw [Set.indicator_of_mem (show y ∈ {y | P y} from hyP)]
        by_contra hne
        have h1 := (hf x y hne).2
        simp at hy
        omega
      · simp [Set.indicator_apply, hyP]
  have key2 : ∀ (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (f : ℕ → ℕ → ℕ),
      (∀ a b, f a b ≠ 0 → a ≤ n ∧ b ≤ n) →
      ∑' s1 : {x | P x}, ∑' s2 : {x | P x}, f s1 s2 =
        ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), if P x ∧ P y then f x y else 0 := by
    intro P _ n f hf
    have h1 : ∀ s1 : {x | P x}, ∑' s2 : {x | P x}, f (s1 : ℕ) (s2 : ℕ) =
        (fun x : ℕ => ∑ y ∈ Finset.range (n + 1), if P y then f x y else 0) (s1 : ℕ) :=
      fun s1 => key1 P n (s1 : ℕ) f hf
    rw [tsum_congr h1]
    rw [tsum_subtype {x | P x} (fun x : ℕ => ∑ y ∈ Finset.range (n + 1), if P y then f x y else 0)]
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x <;> simp [Set.indicator_apply, hx]
    · intro x hx
      have hn : n < x := by simp at hx; omega
      have hz : ∀ y, f x y = 0 := fun y => by
        by_contra hne
        have := (hf x y hne).1
        omega
      simp [Set.indicator_apply, hz]
  have key : ∀ (P : ℕ → Prop) [DecidablePred P] (n : ℕ),
      r {x | P x} n = ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1),
        if P x ∧ P y then (if x ≠ y ∧ x + y = n then 1 else 0) else 0 := by
    intro P _ n
    rw [hr]
    have hc : ∀ s1 s2 : {x | P x}, (if s1 ≠ s2 ∧ (s1 : ℕ) + (s2 : ℕ) = n then 1 else 0 : ℕ) =
        (if (s1 : ℕ) ≠ (s2 : ℕ) ∧ (s1 : ℕ) + (s2 : ℕ) = n then 1 else 0 : ℕ) := by
      intro s1 s2
      simp only [ne_eq, Subtype.ext_iff]
    simp only [hc]
    have hf : ∀ a b : ℕ, (if a ≠ b ∧ a + b = n then 1 else 0 : ℕ) ≠ 0 → a ≤ n ∧ b ≤ n := by
      intro a b h
      by_cases hab : a ≠ b ∧ a + b = n
      · obtain ⟨_, h2⟩ := hab
        exact ⟨by omega, by omega⟩
      · simp [hab] at h
    rw [key2 P n (fun a b => if a ≠ b ∧ a + b = n then 1 else 0) hf]
  have hinner : ∀ n, ∀ x ∈ Finset.range (n + 1),
      ∑ y ∈ Finset.range (n + 1), (if x ≠ y ∧ x + y = n then e x + e y else 0) =
        (if x ≠ n - x then e x + e (n - x) else 0) := by
    intro n x hx
    have hxn : x ≤ n := by
      have := Finset.mem_range.mp hx
      omega
    rw [Finset.sum_eq_single_of_mem (n - x) (Finset.mem_range.mpr (by omega))]
    · by_cases h : x ≠ n - x <;> simp [h, show x + (n - x) = n by omega]
    · intro y hy hne
      rw [if_neg]
      rintro ⟨_, hc⟩
      apply hne
      omega
  have hT : ∀ n, ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1),
      (if x ≠ y ∧ x + y = n then e x + e y else 0) = 0 := by
    intro n
    rw [Finset.sum_congr rfl (hinner n)]
    have hsplit : ∀ x, (if x ≠ n - x then e x + e (n - x) else 0) =
        (e x + e (n - x)) - (if x = n - x then e x + e (n - x) else 0) := by
      intro x
      by_cases h : x = n - x
      · rw [if_neg (fun h' => h' h), if_pos h]
        ring
      · rw [if_pos h, if_neg h]
        ring
    obtain ⟨m, hm⟩ := Nat.even_or_odd' n
    rcases hm with rfl | rfl
    · have hX : ∑ x ∈ Finset.range (2 * m + 1), (e x + e (2 * m - x)) = 2 * e m := by
        rw [Finset.sum_add_distrib]
        have := Finset.sum_range_reflect e (2 * m + 1)
        simp only [Nat.add_sub_cancel] at this
        rw [this, hP m]
        ring
      have hD : ∑ x ∈ Finset.range (2 * m + 1), (if x = 2 * m - x then e x + e (2 * m - x) else 0)
          = 2 * e m := by
        rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))]
        · rw [if_pos (show m = 2 * m - m by omega), show 2 * m - m = m by omega]
          ring
        · intro y hy hne
          rw [if_neg (show ¬ (y = 2 * m - y) by have := Finset.mem_range.mp hy; omega)]
      simp only [hsplit, Finset.sum_sub_distrib, hX, hD, sub_self]
    · have hX : ∑ x ∈ Finset.range (2 * m + 1 + 1), (e x + e (2 * m + 1 - x)) = 0 := by
        rw [Finset.sum_add_distrib]
        have := Finset.sum_range_reflect e (2 * m + 1 + 1)
        simp only [Nat.add_sub_cancel] at this
        simp only [this, hPodd m, add_zero]
      have hD0 : ∑ x ∈ Finset.range (2 * m + 1 + 1),
          (if x = 2 * m + 1 - x then e x + e (2 * m + 1 - x) else 0) = 0 :=
        Finset.sum_eq_zero (fun x _ => by rw [if_neg (show ¬ (x = 2 * m + 1 - x) by omega)])
      simp only [hsplit, Finset.sum_sub_distrib, hX, hD0, sub_zero]
  have hpt : ∀ n x y : ℕ, (2:ℤ) * ((if Even (s x) ∧ Even (s y) then
        (if x ≠ y ∧ x + y = n then 1 else 0) else 0) -
      (if ¬Even (s x) ∧ ¬Even (s y) then (if x ≠ y ∧ x + y = n then 1 else 0) else 0)) =
      (if x ≠ y ∧ x + y = n then e x + e y else 0) := by
    intro n x y
    by_cases hx : Even (s x) <;> by_cases hy : Even (s y) <;>
      by_cases hc : x ≠ y ∧ x + y = n <;> simp [he, hx, hy, hc]
  refine Iff.intro (fun _ => trivial) (fun _ => ?_)
  refine ⟨{x | Even (s x)}, {x | ¬Even (s x)}, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact em (Even (s x))
  · ext x
    simp
  · intro n
    rw [key (fun x => Even (s x)) n, key (fun x => ¬Even (s x)) n]
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have h3 : ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), (2:ℤ) *
        ((if Even (s x) ∧ Even (s y) then (if x ≠ y ∧ x + y = n then 1 else 0) else 0) -
          (if ¬Even (s x) ∧ ¬Even (s y) then (if x ≠ y ∧ x + y = n then 1 else 0) else 0)) = 0 := by
      rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpt n x y))]
      exact hT n
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at h3
    linarith
