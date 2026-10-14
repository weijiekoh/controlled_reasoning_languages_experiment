lemma Ex (n k : ℕ+) (m : ℕ) (hk : (k:ℕ) = n + (m+m)) :
    ∃ g : Fin k → Fin n, ∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0) := by
  have hn := n.pos
  refine ⟨fun j => if h : j.val < n then ⟨j.val, h⟩ else ⟨0, hn⟩, fun i => ?_⟩
  have e : (∑ j : Fin k, if (if h : j.val < n then (⟨j.val, h⟩ : Fin n) else ⟨0, hn⟩) = i then 1 else 0)
      = ∑ v ∈ Finset.range k, (if v < n then (if v = i.val then 1 else 0) else (if i.val = 0 then 1 else 0)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun v => if v < n then (if v = i.val then 1 else 0) else (if i.val = 0 then 1 else 0)) k]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j.val < n
    · simp [h, Fin.ext_iff]
    · simp only [h, dif_neg, not_false_eq_true, if_false]
      exact if_congr (by rw [Fin.ext_iff]; exact eq_comm) rfl rfl
  rw [e, hk, Finset.sum_range_add]
  have e1 : (∑ v ∈ Finset.range n, (if v < n then (if v = i.val then 1 else 0) else (if i.val = 0 then 1 else 0))) = 1 := by
    rw [Finset.sum_congr rfl (g := fun v => if v = i.val then 1 else 0) (fun v hv => by simp at hv; simp [hv])]
    simp [i.isLt]
  have e2 : (∑ v ∈ Finset.range (m+m), (if n + v < n then (if n + v = i.val then 1 else 0) else (if i.val = 0 then 1 else 0))) = if i.val = 0 then m + m else 0 := by
    simp
  rw [e1, e2]
  split_ifs
  · exact ⟨m, by omega⟩
  · simp
