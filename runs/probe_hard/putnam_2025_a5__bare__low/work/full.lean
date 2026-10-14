import Mathlib

open Finset

noncomputable abbrev putnam_2025_a5_solution : (n : ℕ) → Set (Fin n → ℤˣ) := fun n => {s | (∀ i : Fin n, s i = (-1) ^ (i.val + 1)) ∨ (∀ i : Fin n, s i = (-1) ^ i.val)}

def f (n : ℕ) (s : Fin n → ℤˣ) : ℕ :=
  Finset.card {σ : Equiv.Perm (Fin (n + 1)) |
    ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))}

section aux
noncomputable section
def Op (e : ℤˣ) (L : ℕ) (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  if e = 1 then ∑ y ∈ Ico x L, u y else ∑ y ∈ range (min x L), u y

def W : List ℤˣ → ℕ → ℕ
  | [], _ => 1
  | e :: t, x => Op e (t.length + 1) (W t) x

def FF (l : List ℤˣ) : ℕ := ∑ x ∈ range (l.length + 1), W l x

def ng (l : List ℤˣ) : List ℤˣ := l.map (fun e => -e)

lemma Op_mono (e : ℤˣ) (L : ℕ) (u u' : ℕ → ℕ) (h : ∀ y < L, u y ≤ u' y) (x : ℕ) :
    Op e L u x ≤ Op e L u' x := by
  unfold Op
  split_ifs
  · exact sum_le_sum (fun y hy => h y (by simp at hy; omega))
  · exact sum_le_sum (fun y hy => h y (by simp at hy; omega))

lemma Op_strict (e : ℤˣ) (L : ℕ) (u u' : ℕ → ℕ) (h : ∀ y < L, u y ≤ u' y) (y0 : ℕ) (hy0 : y0 < L)
    (hs : u y0 < u' y0) : ∃ x < L + 1, Op e L u x < Op e L u' x := by
  by_cases he : e = 1
  · refine ⟨0, by omega, ?_⟩
    unfold Op
    simp only [he, if_true]
    exact sum_lt_sum (fun y hy => h y (by simp at hy; omega)) ⟨y0, by simp; omega, hs⟩
  · refine ⟨L, by omega, ?_⟩
    unfold Op
    simp only [he, if_false]
    exact sum_lt_sum (fun y hy => h y (by simp at hy; omega)) ⟨y0, by simp; omega, hs⟩

lemma W_mono (p : List ℤˣ) : ∀ (r r' : List ℤˣ), r.length = r'.length →
    (∀ y ≤ r.length, W r y ≤ W r' y) → ∀ x ≤ (p ++ r).length, W (p ++ r) x ≤ W (p ++ r') x := by
  induction p with
  | nil => intro r r' _ h x hx; exact h x hx
  | cons e p ih =>
    intro r r' hl h x hx
    simp only [List.cons_append, W]
    have this : (p ++ r').length = (p ++ r).length := by simp [hl]
    rw [this]
    exact Op_mono _ _ _ _ (fun y hy => ih r r' hl h y (by omega)) x

lemma W_strict (p : List ℤˣ) : ∀ (r r' : List ℤˣ), r.length = r'.length →
    (∀ y ≤ r.length, W r y ≤ W r' y) → (∃ y ≤ r.length, W r y < W r' y) →
    ∃ x ≤ (p ++ r).length, W (p ++ r) x < W (p ++ r') x := by
  induction p with
  | nil => intro r r' _ _ h; exact h
  | cons e p ih =>
    intro r r' hl h hs
    simp only [List.cons_append, W]
    have this : (p ++ r').length = (p ++ r).length := by simp [hl]
    rw [this]
    obtain ⟨y, hy, hlt⟩ := ih r r' hl h hs
    obtain ⟨x, hx, hx2⟩ := Op_strict e ((p ++ r).length + 1) (W (p ++ r)) (W (p ++ r'))
      (fun y hy => W_mono p r r' hl h y (by omega)) y (by omega) hlt
    exact ⟨x, by simp only [List.length_cons]; omega, hx2⟩

lemma ng_length (l : List ℤˣ) : (ng l).length = l.length := by simp [ng]

lemma W_neg : ∀ (l : List ℤˣ) (x : ℕ), x ≤ l.length → W (ng l) x = W l (l.length - x) := by
  intro l
  induction l with
  | nil => intro x _; simp [ng, W]
  | cons e t ih =>
    intro x hx
    have hng : ng (e :: t) = (-e) :: ng t := by simp [ng]
    rw [hng]
    simp only [W, ng_length, List.length_cons]
    simp only [List.length_cons] at hx
    rcases Int.units_eq_one_or e with rfl | rfl
    · have h1 : ¬ ((-1 : ℤˣ) = 1) := by decide
      simp only [Op, h1, if_false, if_true, neg_eq_iff_eq_neg]
      have h2 : min x (t.length + 1) = x := by omega
      rw [h2]
      have := sum_Ico_reflect (W t) 0 (m := x) (n := t.length) (by omega)
      rw [range_eq_Ico]
      rw [show t.length + 1 - 0 = t.length + 1 by omega] at this
      rw [← this]
      refine sum_congr rfl (fun y hy => ?_)
      simp at hy
      rw [ih y (by omega)]
    · have h1 : ¬ ((-1 : ℤˣ) = 1) := by decide
      simp only [Op, h1, if_false, if_true, neg_neg]
      have := sum_Ico_reflect (W t) x (m := t.length + 1) (n := t.length) (by omega)
      have h2 : min (t.length + 1 - x) (t.length + 1) = t.length + 1 - x := by omega
      rw [h2, range_eq_Ico]
      rw [show t.length + 1 - (t.length + 1) = 0 by omega] at this
      rw [← this]
      refine sum_congr rfl (fun y hy => ?_)
      simp at hy
      rw [ih y (by omega)]

lemma W_pos : ∀ t : List ℤˣ, ∃ y ≤ t.length, 0 < W t y := by
  intro t
  induction t with
  | nil => exact ⟨0, le_refl _, by simp [W]⟩
  | cons e t ih =>
    obtain ⟨y, hy, hpos⟩ := ih
    by_cases he : e = 1
    · refine ⟨0, by simp, ?_⟩
      simp only [W, Op, he, if_true]
      exact lt_of_lt_of_le hpos (single_le_sum (f := W t) (fun _ _ => Nat.zero_le _) (by simp; omega))
    · refine ⟨t.length + 1, by simp, ?_⟩
      simp only [W, Op, he, if_false]
      rw [show min (t.length + 1) (t.length + 1) = t.length + 1 by omega]
      exact lt_of_lt_of_le hpos (single_le_sum (f := W t) (fun _ _ => Nat.zero_le _) (by simp; omega))

lemma sumW_pos (t : List ℤˣ) : 0 < ∑ y ∈ range (t.length + 1), W t y := by
  obtain ⟨y, hy, hp⟩ := W_pos t
  exact lt_of_lt_of_le hp (single_le_sum (f := W t) (fun _ _ => Nat.zero_le _) (by simp; omega))

lemma central1 (t : List ℤˣ) :
    (∀ x ≤ (1 :: 1 :: t).length, W (1 :: 1 :: t) x ≤ W (1 :: ng (1 :: t)) x) ∧
    ∃ x ≤ (1 :: 1 :: t).length, W (1 :: 1 :: t) x < W (1 :: ng (1 :: t)) x := by
  have hA : ∀ z z', z' ≤ z → W (1 :: t) z ≤ W (1 :: t) z' := by
    intro z z' h
    simp only [W, Op, if_true]
    exact sum_le_sum_of_subset (by intro y; simp; omega)
  have hlen : (1 :: t).length = t.length + 1 := rfl
  constructor
  · intro x hx
    simp only [List.length_cons] at hx
    show Op 1 ((1 :: t).length + 1) (W (1 :: t)) x ≤ Op 1 ((ng (1 :: t)).length + 1) (W (ng (1 :: t))) x
    simp only [Op, if_true, ng_length]
    have e1 : ∑ y ∈ Ico x ((1 :: t).length + 1), W (ng (1 :: t)) y
        = ∑ y ∈ Ico x ((1 :: t).length + 1), W (1 :: t) ((1 :: t).length - y) := by
      refine sum_congr rfl (fun y hy => ?_)
      simp only [mem_Ico] at hy
      exact W_neg _ _ (by omega)
    rw [e1, sum_Ico_reflect (W (1 :: t)) x (m := (1 :: t).length + 1) (n := (1 :: t).length) (by omega),
      sum_Ico_eq_sum_range]
    rw [show (1 :: t).length + 1 - ((1 :: t).length + 1) = 0 by omega, range_eq_Ico, ← range_eq_Ico]
    refine sum_le_sum (fun k hk => ?_)
    simpa using hA (x + k) k (by omega)
  · refine ⟨t.length + 1, by simp, ?_⟩
    show Op 1 ((1 :: t).length + 1) (W (1 :: t)) (t.length + 1) < Op 1 ((ng (1 :: t)).length + 1) (W (ng (1 :: t))) (t.length + 1)
    simp only [Op, if_true, ng_length, hlen]
    rw [show t.length + 1 + 1 = (t.length + 1) + 1 by rfl, Nat.Ico_succ_singleton, sum_singleton,
      sum_singleton, W_neg _ _ (by simp)]
    have h0 : W (1 :: t) (t.length + 1) = 0 := by simp [W, Op]
    rw [h0, hlen, show t.length + 1 - (t.length + 1) = 0 by omega]
    simpa [W, Op, ← Finset.range_eq_Ico] using sumW_pos t

lemma central2 (t : List ℤˣ) :
    (∀ x ≤ ((-1 : ℤˣ) :: (-1 : ℤˣ) :: t).length, W ((-1 : ℤˣ) :: (-1 : ℤˣ) :: t) x ≤ W ((-1 : ℤˣ) :: ng ((-1 : ℤˣ) :: t)) x) ∧
    ∃ x ≤ ((-1 : ℤˣ) :: (-1 : ℤˣ) :: t).length, W ((-1 : ℤˣ) :: (-1 : ℤˣ) :: t) x < W ((-1 : ℤˣ) :: ng ((-1 : ℤˣ) :: t)) x := by
  have h1 : ¬ ((-1 : ℤˣ) = 1) := by decide
  have hA : ∀ z z', z ≤ z' → W ((-1 : ℤˣ) :: t) z ≤ W ((-1 : ℤˣ) :: t) z' := by
    intro z z' h
    simp only [W, Op, h1, if_false]
    exact sum_le_sum_of_subset (by intro y; simp; omega)
  have hlen : ((-1 : ℤˣ) :: t).length = t.length + 1 := rfl
  constructor
  · intro x hx
    simp only [List.length_cons] at hx
    show Op (-1) (((-1 : ℤˣ) :: t).length + 1) (W ((-1 : ℤˣ) :: t)) x ≤ Op (-1) ((ng ((-1 : ℤˣ) :: t)).length + 1) (W (ng ((-1 : ℤˣ) :: t))) x
    simp only [Op, h1, if_false, ng_length]
    have e1 : ∑ y ∈ range (min x (((-1 : ℤˣ) :: t).length + 1)), W (ng ((-1 : ℤˣ) :: t)) y
        = ∑ y ∈ Ico 0 (min x (((-1 : ℤˣ) :: t).length + 1)), W ((-1 : ℤˣ) :: t) (((-1 : ℤˣ) :: t).length - y) := by
      rw [range_eq_Ico]
      refine sum_congr rfl (fun y hy => ?_)
      simp only [mem_Ico] at hy
      exact W_neg _ _ (by omega)
    rw [e1, sum_Ico_reflect (W ((-1 : ℤˣ) :: t)) 0 (m := min x (((-1 : ℤˣ) :: t).length + 1)) (n := ((-1 : ℤˣ) :: t).length) (by omega),
      sum_Ico_eq_sum_range]
    have e2 : ((-1 : ℤˣ) :: t).length + 1 - 0 - (((-1 : ℤˣ) :: t).length + 1 - min x (((-1 : ℤˣ) :: t).length + 1))
        = min x (((-1 : ℤˣ) :: t).length + 1) := by omega
    rw [e2]
    refine sum_le_sum (fun k hk => ?_)
    simp only [mem_range] at hk
    exact hA _ _ (by omega)
  · refine ⟨1, by simp, ?_⟩
    show Op (-1) (((-1 : ℤˣ) :: t).length + 1) (W ((-1 : ℤˣ) :: t)) 1 < Op (-1) ((ng ((-1 : ℤˣ) :: t)).length + 1) (W (ng ((-1 : ℤˣ) :: t))) 1
    simp only [Op, h1, if_false, ng_length, hlen]
    rw [show min 1 (t.length + 1 + 1) = 1 by omega, sum_range_one, sum_range_one,
      W_neg _ _ (by omega)]
    have h0 : W ((-1 : ℤˣ) :: t) 0 = 0 := by simp [W, Op]
    rw [h0, hlen, show t.length + 1 - 0 = t.length + 1 by omega]
    simpa [W, Op] using sumW_pos t

lemma flip_gt (pre : List ℤˣ) (c : ℤˣ) (t : List ℤˣ) :
    FF (pre ++ c :: c :: t) < FF (pre ++ c :: ng (c :: t)) := by
  have hc : (c :: c :: t) = c :: (c :: t) := rfl
  have key : (∀ x ≤ (c :: c :: t).length, W (c :: c :: t) x ≤ W (c :: ng (c :: t)) x) ∧
    ∃ x ≤ (c :: c :: t).length, W (c :: c :: t) x < W (c :: ng (c :: t)) x := by
    rcases Int.units_eq_one_or c with rfl | rfl
    · exact central1 t
    · exact central2 t
  have hl : (c :: c :: t).length = (c :: ng (c :: t)).length := by simp [ng_length]
  have hm := W_mono pre _ _ hl key.1
  obtain ⟨x, hx, hxx⟩ := W_strict pre _ _ hl key.1 key.2
  have e1 : (pre ++ c :: c :: t).length = (pre ++ c :: ng (c :: t)).length := by simp [ng_length]
  unfold FF
  rw [← e1]
  refine sum_lt_sum (fun y hy => hm y (by rw [mem_range] at hy; omega)) ⟨x, by rw [mem_range]; omega, hxx⟩

lemma FF_ng (l : List ℤˣ) : FF (ng l) = FF l := by
  unfold FF
  rw [ng_length]
  have : ∀ x ∈ range (l.length + 1), W (ng l) x = W l (l.length - x) := fun x hx =>
    W_neg l x (by simp at hx; omega)
  rw [sum_congr rfl this]
  have := sum_range_reflect (W l) (l.length + 1)
  simpa using this
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


lemma mk_cond {n : ℕ} (s : Fin (n+1) → ℤˣ) (x : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
    (mkP x τ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((mkP x τ i.succ : ℤ) - (mkP x τ i.castSucc : ℤ))) ↔
    ((if s 0 = 1 then x.val ≤ (τ 0).val else (τ 0).val < x.val) ∧
      ∀ i : Fin n, 0 < (s i.succ : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) := by
  rw [Fin.forall_fin_succ]
  simp only [mkP_zero, true_and, Fin.castSucc_zero, mkP_succ]
  rw [key_x]
  refine and_congr Iff.rfl (forall_congr' (fun i => ?_))
  rw [← Fin.succ_castSucc, mkP_succ, key_pair]

lemma partA_step (n : ℕ) (s : Fin (n+1) → ℤˣ) (x : Fin (n+2))
    (ih : ∀ (s : Fin n → ℤˣ) (x : Fin (n+1)),
      (univ.filter (fun σ : Equiv.Perm (Fin (n+1)) => σ 0 = x ∧ ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val) :
    (univ.filter (fun σ : Equiv.Perm (Fin (n+2)) => σ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val := by
  rw [List.ofFn_succ]
  have hW : W (s 0 :: List.ofFn fun i => s i.succ) x.val
      = Op (s 0) (n+1) (W (List.ofFn fun i => s i.succ)) x.val := by simp [W]
  rw [hW]
  set T : Finset (Equiv.Perm (Fin (n+1))) := univ.filter (fun τ : Equiv.Perm (Fin (n+1)) =>
    (if s 0 = 1 then x.val ≤ (τ 0).val else (τ 0).val < x.val) ∧
      ∀ i : Fin n, 0 < (s i.succ : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) with hT
  have h1 : T.card = (univ.filter (fun σ : Equiv.Perm (Fin (n+2)) => σ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card := by
    refine Finset.card_nbij (mkP x) ?_ ?_ ?_
    · intro τ hτ
      rw [mem_coe, hT, mem_filter] at hτ
      rw [mem_coe, mem_filter]
      exact ⟨mem_univ _, (mk_cond s x τ).2 hτ.2⟩
    · intro τ _ τ' _ h
      refine Equiv.ext (fun i => ?_)
      have := congrArg (fun σ => σ i.succ) h
      simp only [mkP_succ] at this
      exact Fin.succAbove_right_injective this
    · intro σ hσ
      rw [mem_coe, mem_filter] at hσ
      obtain ⟨hσ0, hσc⟩ := hσ.2
      have hne : ∀ i : Fin (n+1), σ i.succ ≠ x := by
        intro i h
        rw [← hσ0] at h
        exact Fin.succ_ne_zero i (σ.injective h)
      set ψ : Fin (n+2) → Fin (n+1) := Function.invFun x.succAbove with hψdef
      have hψ : ∀ i : Fin (n+1), x.succAbove (ψ (σ i.succ)) = σ i.succ := fun i =>
        Function.invFun_eq (Fin.exists_succAbove_eq (hne i))
      have inj : Function.Injective (fun i : Fin (n+1) => ψ (σ i.succ)) := by
        intro a b h
        have := hψ a
        simp only at h
        rw [h, hψ b] at this
        exact Fin.succ_injective _ (σ.injective this.symm)
      set τ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 inj) with hτ
      have heq : mkP x τ = σ := by
        ext j
        induction j using Fin.cases with
        | zero => rw [mkP_zero, hσ0]
        | succ i => rw [mkP_succ]; exact congrArg Fin.val (hψ i)
      refine ⟨τ, ?_, heq⟩
      rw [mem_coe, hT, mem_filter]
      refine ⟨mem_univ _, (mk_cond s x τ).1 (by rw [heq]; exact ⟨hσ0, hσc⟩)⟩
  rw [← h1]
  have h2 := Finset.card_eq_sum_card_fiberwise (f := fun τ : Equiv.Perm (Fin (n+1)) => τ 0) (s := T) (t := univ) (by simp)
  rw [h2]
  have h3 : ∀ y : Fin (n+1), (T.filter (fun τ => τ 0 = y)).card =
      if (if s 0 = 1 then x.val ≤ y.val else y.val < x.val) then W (List.ofFn fun i => s i.succ) y.val else 0 := by
    intro y
    by_cases hr : (if s 0 = 1 then x.val ≤ y.val else y.val < x.val)
    · rw [if_pos hr, ← ih (fun i => s i.succ) y]
      congr 1
      ext τ
      simp only [hT, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, h⟩, h0⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨⟨by rw [h0]; exact hr, h⟩, h0⟩
    · rw [if_neg hr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro τ hτ h0
      rw [hT, mem_filter] at hτ
      rw [h0] at hτ
      exact hr hτ.2.1
  rw [sum_congr rfl (fun y _ => h3 y)]
  rw [Fin.sum_univ_eq_sum_range (fun y => if (if s 0 = 1 then x.val ≤ y else y < x.val) then W (List.ofFn fun i => s i.succ) y else 0) (n+1)]
  unfold Op
  by_cases he : s 0 = 1
  · simp only [he, if_true]
    rw [← sum_filter]
    refine sum_congr ?_ (fun _ _ => rfl)
    ext y; simp; omega
  · simp only [he, if_false]
    rw [← sum_filter]
    refine sum_congr ?_ (fun _ _ => rfl)
    ext y; simp; omega

lemma partA : ∀ (n : ℕ) (s : Fin n → ℤˣ) (x : Fin (n+1)),
    (univ.filter (fun σ : Equiv.Perm (Fin (n+1)) => σ 0 = x ∧ ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val := by
  intro n
  induction n with
  | zero => intro s x; rw [partA_zero]; simp [W]
  | succ n ih => exact fun s x => partA_step n s x ih

def altL (a : ℤˣ) : ℕ → List ℤˣ
  | 0 => []
  | k+1 => a :: altL (-a) k

lemma altL_len (a : ℤˣ) (k : ℕ) : (altL a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [altL, ih]

lemma altL_neg (a : ℤˣ) (k : ℕ) : altL (-a) k = ng (altL a k) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [altL, ng, List.map_cons, List.map_map] at ih ⊢; have := ih (-a); rw [neg_neg] at this; rw [this]

lemma altL_snoc (a : ℤˣ) (k : ℕ) : ∃ c, altL a (k+1) = altL a k ++ [c] ∧ altL a (k+2) = altL a k ++ [c, -c] := by
  induction k generalizing a with
  | zero => exact ⟨a, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨c, h1, h2⟩ := ih (-a)
    refine ⟨c, ?_, ?_⟩
    · show a :: altL (-a) (k+1) = a :: altL (-a) k ++ [c]
      rw [h1]; rfl
    · show a :: altL (-a) (k+2) = a :: altL (-a) k ++ [c, -c]
      rw [h2]; rfl

lemma neg_of_ne (b c : ℤˣ) (h : b ≠ c) : b = -c := by
  rcases Int.units_eq_one_or b with rfl | rfl <;> rcases Int.units_eq_one_or c with rfl | rfl <;> first | rfl | exact absurd rfl h | decide

lemma Zlem : ∀ (d k : ℕ) (a : ℤˣ) (rest : List ℤˣ), 1 ≤ k → rest.length = d →
    FF (altL a k ++ rest) ≤ FF (altL a (k + d)) := by
  intro d
  induction d with
  | zero =>
    intro k a rest _ hr
    have : rest = [] := List.length_eq_zero_iff.mp hr
    subst this
    simp
  | succ d ih =>
    intro k a rest hk hr
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, rest', rfl⟩ : ∃ b rest', rest = b :: rest' := by
      cases rest with
      | nil => simp at hr
      | cons b r => exact ⟨b, r, rfl⟩
    have hr' : rest'.length = d := by simpa using hr
    obtain ⟨c, h1, h2⟩ := altL_snoc a j
    by_cases hb : b = c
    · subst hb
      have e1 : altL a (j+1) ++ b :: rest' = altL a j ++ b :: b :: rest' := by rw [h1]; simp
      have e2 : altL a j ++ b :: ng (b :: rest') = altL a (j+2) ++ ng rest' := by
        rw [h2]; simp [ng]
      have := flip_gt (altL a j) b rest'
      rw [e1]
      refine le_trans this.le ?_
      rw [e2]
      have := ih (j+2) a (ng rest') (by omega) (by rw [ng_length]; exact hr')
      rw [show j + 1 + (d + 1) = j + 2 + d by omega]
      exact this
    · have hb' := neg_of_ne b c hb
      have e1 : altL a (j+1) ++ b :: rest' = altL a (j+2) ++ rest' := by
        rw [h1, h2, hb']; simp
      rw [e1]
      have := ih (j+2) a rest' (by omega) hr'
      rw [show j + 1 + (d + 1) = j + 2 + d by omega]
      exact this

lemma decomp : ∀ (l : List ℤˣ) (a : ℤˣ), (∃ pre c rest, l = pre ++ c :: c :: rest) ∨
    l = altL a l.length ∨ (∃ b l₁, l = b :: l₁ ∧ b ≠ a) := by
  intro l
  induction l with
  | nil => intro a; exact Or.inr (Or.inl rfl)
  | cons b l₁ ih =>
    intro a
    by_cases hba : b = a
    · subst hba
      rcases ih (-b) with ⟨pre, c, rest, h⟩ | h | ⟨b', l₂, h, hne⟩
      · exact Or.inl ⟨b :: pre, c, rest, by simp [h]⟩
      · exact Or.inr (Or.inl (by simp [altL, ← h]))
      · have : b' = b := by have := neg_of_ne b' (-b) hne; simpa using this
        subst this
        exact Or.inl ⟨[], b', l₂, by simp [h]⟩
    · exact Or.inr (Or.inr ⟨b, l₁, rfl, hba⟩)

lemma ofFn_alt (a : ℤˣ) : ∀ (n : ℕ) (s : Fin n → ℤˣ), (∀ i : Fin n, s i = a * (-1)^i.val) → List.ofFn s = altL a n := by
  intro n
  induction n generalizing a with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    rw [List.ofFn_succ]
    simp only [altL]
    congr 1
    · simpa using h 0
    · apply ih
      intro i
      rw [h i.succ]
      simp [pow_succ]
      
lemma alt_ofFn (a : ℤˣ) : ∀ (n : ℕ) (s : Fin n → ℤˣ), List.ofFn s = altL a n → (∀ i : Fin n, s i = a * (-1)^i.val) := by
  intro n
  induction n generalizing a with
  | zero => intro s _ i; exact i.elim0
  | succ n ih =>
    intro s h i
    rw [List.ofFn_succ] at h
    simp only [altL, List.cons.injEq] at h
    induction i using Fin.cases with
    | zero => simpa using h.1
    | succ i =>
      have := ih (-a) _ h.2 i
      rw [this]
      simp [pow_succ]

lemma f_eq (n : ℕ) (s : Fin n → ℤˣ) : f n s = FF (List.ofFn s) := by
  unfold f FF
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (n+1)) => σ 0) (t := univ) (by simp)]
  have : ∀ y : Fin (n+1), (({σ : Equiv.Perm (Fin (n + 1)) |
      ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))}).filter (fun σ => σ 0 = y)).card
      = W (List.ofFn s) y.val := by
    intro y
    rw [← partA n s y]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [sum_congr rfl (fun y _ => this y)]
  rw [Fin.sum_univ_eq_sum_range (fun y => W (List.ofFn s) y) (n+1)]
  simp

lemma exists_ofFn (n : ℕ) (l' : List ℤˣ) (h : l'.length = n) : ∃ t : Fin n → ℤˣ, List.ofFn t = l' := by
  subst h; exact ⟨l'.get, List.ofFn_get l'⟩

lemma FF_alt (a b : ℤˣ) (n : ℕ) : FF (altL a n) = FF (altL b n) := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
  · rfl
  · rw [altL_neg 1 n, FF_ng]
  · rw [altL_neg 1 n, FF_ng]
  · rfl
end
end aux
/--
Let $n$ be an integer with $n \ge 2$. For a sequence $s = (s_1, \ldots, s_{n-1})$ where each
$s_i = \pm 1$, let $f(s)$ be the number of permutations $(a_1, \ldots, a_n)$ of $\{1, 2, \ldots, n\}$
such that $s_i(a_{i+1} - a_i) > 0$ for all $i$. For each $n$, determine the sequences $s$ for which
$f(s)$ is maximal.
-/

theorem putnam_2025_a5
    (n : ℕ)
    (hn : 1 ≤ n)
    (s : Fin n → ℤˣ) :
    (∀ t : Fin n → ℤˣ, f n t ≤ f n s) ↔ s ∈ putnam_2025_a5_solution n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  constructor
  · intro hmax
    by_contra hns
    rcases decomp (List.ofFn s) (s 0) with ⟨pre, c, rest, h⟩ | h | ⟨b, l₁, h, hne⟩
    · have hg := flip_gt pre c rest
      have hlen : (pre ++ c :: ng (c :: rest)).length = m + 1 := by
        have := congrArg List.length h
        simp only [List.length_ofFn, List.length_append, List.length_cons, ng_length] at this ⊢
        omega
      obtain ⟨t, ht⟩ := exists_ofFn (m+1) _ hlen
      have := hmax t
      rw [f_eq, f_eq, ht, h] at this
      omega
    · apply hns
      rw [List.length_ofFn] at h
      have := alt_ofFn _ _ s h
      rcases Int.units_eq_one_or (s 0) with ha | ha
      · right
        intro i
        rw [this i, ha, one_mul]
      · left
        intro i
        rw [this i, ha, pow_succ']
    · rw [List.ofFn_succ] at h
      exact hne (List.cons.inj h).1.symm
  · intro hs t
    have hs' : FF (List.ofFn s) = FF (altL (-1) (m+1)) := by
      rcases hs with h | h
      · rw [ofFn_alt (-1) (m+1) s (fun i => by rw [h i, pow_succ']) ]
      · rw [ofFn_alt 1 (m+1) s (fun i => by rw [h i, one_mul]), FF_alt 1 (-1)]
    rw [f_eq, f_eq, hs']
    have hz := Zlem m 1 (t 0) (List.ofFn fun i : Fin m => t i.succ) le_rfl (by simp)
    have e : altL (t 0) 1 ++ List.ofFn (fun i : Fin m => t i.succ) = List.ofFn t := by
      rw [List.ofFn_succ]; rfl
    rw [e] at hz
    refine le_trans hz ?_
    rw [FF_alt (t 0) (-1), add_comm]
