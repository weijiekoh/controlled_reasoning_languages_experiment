lemma sa_val {n : ℕ} (x : Fin (n+1)) (y : Fin n) :
    (x.succAbove y).val = if y.val < x.val then y.val else y.val + 1 := by
  unfold Fin.succAbove
  by_cases h : y.castSucc < x
  · rw [if_pos h, if_pos (by simpa [Fin.lt_def] using h)]; simp
  · rw [if_neg h, if_neg (by simpa [Fin.lt_def] using h)]; simp

def mkF {n : ℕ} (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : Fin (n+2) → Fin (n+2) :=
  Fin.cons (α := fun _ => Fin (n+2)) x (fun i => x.succAbove (τ i))

lemma mkF_inj {n : ℕ} (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : Function.Injective (mkF x τ) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => simp [mkF] at h
  | succ a =>
    induction b using Fin.cases with
    | zero => simp [mkF] at h
    | succ b =>
      simp [mkF] at h
      rw [h]

noncomputable def mkP {n : ℕ} (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin (n+2)) :=
  Equiv.ofBijective (mkF x τ) (Finite.injective_iff_bijective.1 (mkF_inj x τ))

lemma mkP_zero {n : ℕ} (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : mkP x τ 0 = x := by
  simp [mkP, mkF]

lemma mkP_succ {n : ℕ} (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    mkP x τ i.succ = x.succAbove (τ i) := by
  simp [mkP, mkF]

lemma key_pair {n : ℕ} (x : Fin (n+2)) (e : ℤˣ) (a b : Fin (n+1)) :
    (0 < (e : ℤ) * (((x.succAbove a : Fin (n+2)) : ℤ) - ((x.succAbove b : Fin (n+2)) : ℤ))) ↔
    (0 < (e : ℤ) * ((a : ℤ) - (b : ℤ))) := by
  rcases Int.units_eq_one_or e with rfl | rfl <;>
  · simp only [sa_val, Units.val_one, Units.val_neg]
    split_ifs <;> omega

lemma key_x {n : ℕ} (x : Fin (n+2)) (e : ℤˣ) (y : Fin (n+1)) :
    (0 < (e : ℤ) * (((x.succAbove y : Fin (n+2)) : ℤ) - (x : ℤ))) ↔
    (if e = 1 then x.val ≤ y.val else y.val < x.val) := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp only [sa_val, Units.val_one, if_true]
    split_ifs <;> omega
  · have h1 : ¬ ((-1 : ℤˣ) = 1) := by decide
    simp only [sa_val, Units.val_neg, Units.val_one, h1, if_false]
    split_ifs <;> omega

lemma partA_zero (s : Fin 0 → ℤˣ) (x : Fin 1) :
    (univ.filter (fun σ : Equiv.Perm (Fin 1) => σ 0 = x ∧ ∀ i : Fin 0, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro _; exact Subsingleton.elim _ _
  · intro _; exact ⟨Subsingleton.elim _ _, fun i => i.elim0⟩

lemma partA_step (n : ℕ) (s : Fin (n+1) → ℤˣ) (x : Fin (n+2))
    (ih : ∀ (s : Fin n → ℤˣ) (x : Fin (n+1)),
      (univ.filter (fun σ : Equiv.Perm (Fin (n+1)) => σ 0 = x ∧ ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val) :
    (univ.filter (fun σ : Equiv.Perm (Fin (n+2)) => σ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val := by
  sorry
