import Mathlib

open MvPolynomial Set

noncomputable abbrev putnam_2003_a6_solution : Prop := True
def pc (n : ℕ) : ℕ := (Nat.digits 2 n).sum

def ε (n : ℕ) : ℤ := if pc n % 2 = 0 then 1 else -1

lemma pc_succ (n : ℕ) : pc n = n % 2 + pc (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pc]
  · unfold pc
    rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]

lemma ε_even (m : ℕ) : ε (2*m) = ε m := by
  unfold ε
  rw [pc_succ (2*m)]
  have h1 : 2*m % 2 = 0 := by omega
  have h2 : 2*m / 2 = m := by omega
  rw [h1, h2]
  simp

lemma ε_odd (m : ℕ) : ε (2*m+1) = - ε m := by
  unfold ε
  rw [pc_succ (2*m+1)]
  have h1 : (2*m+1) % 2 = 1 := by omega
  have h2 : (2*m+1) / 2 = m := by omega
  rw [h1, h2]
  split_ifs <;> omega

lemma ε_sum (m : ℕ) : ∑ a ∈ Finset.range (2*m), ε a = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      ε_odd, ε_even]
    ring

lemma reflect_sum (g : ℕ → ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), g (n - a) = ∑ a ∈ Finset.range (n+1), g a := by
  have := Finset.sum_range_reflect g (n+1)
  simpa using this

open Classical in
lemma Z_zero (n : ℕ) : ∑ a ∈ Finset.range (n+1), (if a ≠ n - a then ε a else 0) = 0 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2, by omega⟩
  · have hp : ∀ a ∈ Finset.range (2*m+1), (if a ≠ 2*m - a then ε a else 0)
        = ε a - (if a = m then ε a else 0) := by
      intro a ha
      simp only [Finset.mem_range] at ha
      split_ifs <;> first | omega | ring | skip
    rw [Finset.sum_congr rfl hp, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    rw [if_pos (by omega), Finset.sum_range_succ, ε_sum, ε_even]
    ring
  · have hp : ∀ a ∈ Finset.range (2*m+1+1), (if a ≠ 2*m+1 - a then ε a else 0) = ε a := by
      intro a ha
      simp only [Finset.mem_range] at ha
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hp, show 2*m+1+1 = 2*(m+1) by ring, ε_sum]

open Classical in
lemma inner_collapse (P : ℕ → Prop) [DecidablePred P] (n a : ℕ) (ha : a ≤ n) :
    ∑ b ∈ Finset.range (n+1), (if b ∈ {k : ℕ | P k} then (if (a ≠ b ∧ a + b = n) then (1:ℕ) else 0) else 0)
      = if (n - a ∈ {k : ℕ | P k} ∧ a ≠ n - a) then 1 else 0 := by
  have hsum : a + (n - a) = n := by omega
  have hmem : n - a ∈ Finset.range (n+1) := by simp only [Finset.mem_range]; omega
  have h0 : ∀ b ∈ Finset.range (n+1), b ≠ n - a →
      (if b ∈ {k : ℕ | P k} then (if (a ≠ b ∧ a + b = n) then (1:ℕ) else 0) else 0) = 0 := by
    intro b _ hne
    split_ifs with h1 h2 <;> first | rfl | omega
  rw [Finset.sum_eq_single (n - a) h0 (fun h => absurd hmem h)]
  by_cases h1 : P (n - a) <;> by_cases h2 : a ≠ n - a <;> simp [h1, h2, hsum]

open Classical in
lemma tsum_sub (S : Set ℕ) (f : ℕ → ℕ) (n : ℕ) (hf : ∀ a, n < a → f a = 0) :
    ∑' s : S, f s = ∑ a ∈ Finset.range (n+1), if a ∈ S then f a else 0 := by
  rw [tsum_subtype S f, tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro a _
    simp [Set.indicator]
  · intro a ha
    simp only [Finset.mem_range, not_lt] at ha
    simp [Set.indicator, hf a (by omega)]

open Classical in
lemma r_formula (r : Set ℕ → ℕ → ℕ)
  (hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0) (S : Set ℕ) (n : ℕ) :
  r S n = ∑ a ∈ Finset.range (n+1), if a ∈ S then ∑ b ∈ Finset.range (n+1), if b ∈ S then (if (a ≠ b ∧ a + b = n) then 1 else 0) else 0 else 0 := by
  set G : ℕ → ℕ := fun a => ∑' s2 : S, if ((a:ℕ) ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) then 1 else 0 with hG
  have h1 : r S n = ∑' s1 : S, G s1 := by
    rw [hr]
    apply tsum_congr
    intro s1
    simp only [hG, ne_eq, Subtype.ext_iff]
  have hG0 : ∀ a, n < a → G a = 0 := by
    intro a ha
    have : ∀ s2 : S, ¬ (a ≠ (s2:ℕ) ∧ a + (s2:ℕ) = n) := fun s2 h => by omega
    simp only [hG, this, if_false, tsum_zero]
  rw [h1, tsum_sub S G n hG0]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with haS
  · refine (tsum_sub S (fun b => if (a ≠ b ∧ a + b = n) then 1 else 0) n ?_).trans ?_
    · intro b hb
      have : ¬ (a ≠ b ∧ a + b = n) := fun h => by omega
      simp [this]
    · rfl
  · rfl

open Classical in
lemma final_sum (n : ℕ) :
    ∑ a ∈ Finset.range (n+1), (if a ∈ {k : ℕ | pc k % 2 = 0} then
      ∑ b ∈ Finset.range (n+1), (if b ∈ {k : ℕ | pc k % 2 = 0} then (if (a ≠ b ∧ a + b = n) then 1 else 0) else 0) else 0)
    = ∑ a ∈ Finset.range (n+1), (if a ∈ {k : ℕ | ¬ pc k % 2 = 0} then
      ∑ b ∈ Finset.range (n+1), (if b ∈ {k : ℕ | ¬ pc k % 2 = 0} then (if (a ≠ b ∧ a + b = n) then 1 else 0) else 0) else 0) := by
  have hcol : ∀ (P : ℕ → Prop) [DecidablePred P], ∑ a ∈ Finset.range (n+1), (if a ∈ {k : ℕ | P k} then
      ∑ b ∈ Finset.range (n+1), (if b ∈ {k : ℕ | P k} then (if (a ≠ b ∧ a + b = n) then 1 else 0) else 0) else 0)
      = ∑ a ∈ Finset.range (n+1), (if a ∈ {k : ℕ | P k} then (if (n - a ∈ {k : ℕ | P k} ∧ a ≠ n - a) then 1 else 0) else 0) := by
    intro P _
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ n := by simp only [Finset.mem_range] at ha; omega
    by_cases h : a ∈ {k : ℕ | P k}
    · rw [if_pos h, if_pos h]
      exact inner_collapse P n a ha'
    · rw [if_neg h, if_neg h]
  rw [hcol (fun k => pc k % 2 = 0), hcol (fun k => ¬ pc k % 2 = 0)]
  have key : ∀ a ∈ Finset.range (n+1),
      2 * (((if a ∈ {k : ℕ | pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ)
        - ((if a ∈ {k : ℕ | ¬ pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | ¬ pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ))
      = (if a ≠ n - a then ε a else 0) + (if n - a ≠ n - (n - a) then ε (n - a) else 0) := by
    intro a ha
    have ha' : a ≤ n := by simp only [Finset.mem_range] at ha; omega
    have hnn : n - (n - a) = a := by omega
    rw [hnn]
    simp only [Set.mem_setOf_eq]
    unfold ε
    split_ifs <;> omega
  have R := reflect_sum (fun a => if a ≠ n - a then ε a else 0) n
  have H : ∑ a ∈ Finset.range (n+1), 2 * (((if a ∈ {k : ℕ | pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ)
        - ((if a ∈ {k : ℕ | ¬ pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | ¬ pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ))
      = 0 := by
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, R, Z_zero]
    simp
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at H
  have H2 : ∑ a ∈ Finset.range (n+1), (((if a ∈ {k : ℕ | pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ))
      = ∑ a ∈ Finset.range (n+1), (((if a ∈ {k : ℕ | ¬ pc k % 2 = 0} then (if (n - a ∈ {k : ℕ | ¬ pc k % 2 = 0} ∧ a ≠ n - a) then 1 else 0) else 0 : ℕ) : ℤ)) := by
    linarith
  exact_mod_cast H2

theorem putnam_2003_a6
(r : Set ℕ → ℕ → ℕ)
(hr : ∀ S n, r S n = ∑' s1 : S, ∑' s2 : S, if (s1 ≠ s2 ∧ s1 + s2 = n) then 1 else 0)
: (∃ A B : Set ℕ, A ∪ B = (Set.univ : Set ℕ) ∧ A ∩ B = ∅ ∧ (∀ n : ℕ, r A n = r B n)) ↔ putnam_2003_a6_solution :=
by
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨{k : ℕ | pc k % 2 = 0}, {k : ℕ | ¬ pc k % 2 = 0}, ?_, ?_, ?_⟩
    · ext k
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact em _
    · ext k
      simp
    · intro n
      rw [r_formula r hr, r_formula r hr]
      convert final_sum n
