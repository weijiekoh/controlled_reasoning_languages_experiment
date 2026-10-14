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
  have hle : ∀ i j, M i j ≤ n^2 := fun i j => by
    have := (Finset.mem_Icc.mp (hM.mem i j)).2
    rw [sq]; exact this
  have hge : ∀ i j, 1 ≤ M i j := fun i j => (Finset.mem_Icc.mp (hM.mem i j)).1
  have sumrep : ∀ (f : Fin n → ℕ), (∀ j, f j ≤ n^2) →
      ∑ j, (n^2 + 1 - f j) = n * (n^2+1) - ∑ j, f j := by
    intro f hf
    have hfj : ∀ j, f j ≤ n^2 + 1 := fun j => by
      have := hf j; rw [sq] at this ⊢; exact Nat.le_succ_of_le this
    have key : ∑ j, (n^2 + 1 - f j) + ∑ j, f j = n * (n^2+1) := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun j _ => tsub_add_cancel_of_le (hfj j))]
      simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.eq_sub_of_add_eq key
  constructor
  · intro i j
    have h1 := hle i j
    have h2 := hge i j
    rw [Finset.mem_Icc]
    simp only [replace]
    constructor
    · omega
    · have : n^2 + 1 - M i j ≤ n*n := by rw [← sq]; omega
      exact this
  · intro i j i' j' h heq
    apply hM.pairwise i j i' j' h
    simp only [replace] at heq
    have := hle i j
    have := hle i' j'
    omega
  · obtain ⟨s, hr, hc, hd, hd'⟩ := hM.same_sum
    refine ⟨n * (n^2+1) - s, ?_, ?_, ?_, ?_⟩
    · intro i
      have := sumrep (fun j => M i j) (fun j => hle i j)
      show ∑ j, (n^2 + 1 - _) = _
      rw [this, hr i]
    · intro j
      have := sumrep (fun i => M i j) (fun i => hle i j)
      show ∑ j, (n^2 + 1 - _) = _
      rw [this, hc j]
    · have := sumrep (fun i => M i i.rev) (fun i => hle i i.rev)
      show ∑ j, (n^2 + 1 - _) = _
      rw [this, hd]
    · have := sumrep (fun i => M i i) (fun i => hle i i)
      show ∑ j, (n^2 + 1 - _) = _
      rw [this, hd']
