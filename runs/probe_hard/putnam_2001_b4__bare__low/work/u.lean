
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
