s/^      simpa using this$/      have e : Set.range ![u, v] = {u, v} := by ext; simp [Fin.exists_fin_two, eq_comm]\n      rw [e] at this; simpa using this/
s/^    by_cases hr0 : r ≤ 0$/    show r ≤ Real.sqrt 2 \/ 2\n    by_cases hr0 : r ≤ 0/
s/^    have hu1 : ‖u‖ = 1 := by simpa \[hu\] using .*/    have hu1 : ‖u‖ = 1 := by rw [hu]; exact b0.orthonormal.1 0/
s/^    have hv1 : ‖v‖ = 1 := by simpa \[hv\] using .*/    have hv1 : ‖v‖ = 1 := by rw [hv]; exact b0.orthonormal.1 1/
s/^      have := b0.orthonormal.2 (show.*/      have := b0.orthonormal.2 (show (0:Fin 2) ≠ 1 by decide)\n      rw [hu, hv]; exact this/
/^      simpa \[hu, hv\] using this$/d
s/^      nlinarith$/      rw [← hs2]; nlinarith [mul_pos hr0 hspos]/
