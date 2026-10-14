import Mathlib

structure IsMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop where
  mem : ∀ i j, M i j ∈ Finset.Icc 1 (n * n)
  pairwise : ∀ i j i' j', i ≠ i' ∨ j ≠ j' → M i j ≠ M i' j'
  same_sum : ∃ s, (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) ∧ (∑ i, M i i.rev = s) ∧ ∑ i, M i i = s

abbrev replace {n : ℕ}: Matrix (Fin n) (Fin n) ℕ → Matrix (Fin n) (Fin n) ℕ :=
  fun A i j ↦ n^2 + 1 - A i j

/--
Show that the result of replacing every integer a in a magic square of order n with $n^2 + 1 − a$ is a magic square of order n.
-/
theorem brualdi_ch1_16 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) (hM : IsMagicSquare M) :
    IsMagicSquare (replace M) := by
  obtain ⟨s, h1, h2, h3, h4⟩ := hM.same_sum
  have hb : ∀ i j, M i j ≤ n^2 + 1 := by
    intro i j
    have := (Finset.mem_Icc.mp (hM.mem i j)).2
    nlinarith
  have key : ∀ f : Fin n → ℕ, (∀ j, f j ≤ n^2+1) →
      ∑ j, (n^2+1 - f j) + ∑ j, f j = n*(n^2+1) := by
    intro f hf
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hf j))]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have := (Finset.mem_Icc.mp (hM.mem i j))
    simp only [replace, Finset.mem_Icc]
    constructor <;> nlinarith [Nat.sub_add_cancel (hb i j)]
  · intro i j i' j' h hEq
    have a := hb i j
    have b := hb i' j'
    have := (Finset.mem_Icc.mp (hM.mem i j))
    have := (Finset.mem_Icc.mp (hM.mem i' j'))
    simp only [replace] at hEq
    have : M i j = M i' j' := by omega
    exact hM.pairwise i j i' j' h this
  · refine ⟨n*(n^2+1) - s, ?_, ?_, ?_, ?_⟩
    · intro i
      have := key (fun j => M i j) (hb i)
      have := h1 i
      simp only [replace]; omega
    · intro j
      have := key (fun i => M i j) (fun i => hb i j)
      have := h2 j
      simp only [replace]; omega
    · have := key (fun i => M i i.rev) (fun i => hb i _)
      simp only [replace]; omega
    · have := key (fun i => M i i) (fun i => hb i _)
      simp only [replace]; omega
