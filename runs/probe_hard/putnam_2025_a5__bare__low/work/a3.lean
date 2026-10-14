
lemma mk_cond {n : ℕ} (s : Fin (n+1) → ℤˣ) (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
    (mkP x τ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((mkP x τ i.succ : ℤ) - (mkP x τ i.castSucc : ℤ))) ↔
    ((if s 0 = 1 then x.val ≤ (τ 0).val else (τ 0).val < x.val) ∧
      ∀ i : Fin n, 0 < (s i.succ : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) := by
  rw [Fin.forall_fin_succ]
  simp only [mkP_zero, true_and, Fin.castSucc_zero, mkP_succ]
  rw [key_x]
  refine and_congr Iff.rfl (forall_congr' (fun i => ?_))
  rw [← Fin.succ_castSucc, mkP_succ, key_pair]
