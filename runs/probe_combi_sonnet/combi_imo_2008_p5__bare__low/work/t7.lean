theorem imo_2008_p5 (n k : ℕ+) (hnk : k ≥ n) (hnk' : Even (k - n)) :
    N n k / M n k = imo_2008_p5_solution n k := by
  obtain ⟨r, hr⟩ := hnk'
  have h1 := congrArg PNat.val hr
  rw [PNat.add_coe, PNat.sub_coe] at h1
  have hr1 := r.pos
  have hle : (n:ℕ) ≤ k := hnk
  have hk : (k:ℕ) = n + ((r:ℕ) + r) := by
    split_ifs at h1 with h
    · have : (n:ℕ) < k := h
      omega
    · omega
  obtain ⟨h2, h3⟩ := mainN n k hle (Ex n k r hk)
  rw [h2]
  have h4 : (M n k : ℝ) ≠ 0 := by exact_mod_cast h3.ne'
  simp only [imo_2008_p5_solution]
  push_cast
  field_simp
  rfl
