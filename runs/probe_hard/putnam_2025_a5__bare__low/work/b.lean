import Mathlib
open Finset

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
