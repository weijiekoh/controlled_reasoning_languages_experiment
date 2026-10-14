import Mathlib

def switch_lamp (n : ℕ+) (switch_label : Fin (2 * n)) (lamps_state : List Bool) : List Bool :=
  List.mapIdx (fun j (x : Bool) => if j = switch_label then ¬x else x) lamps_state

def lamps_final_state (n : ℕ+) (switch_list : List (Fin (2 * n))) : List Bool :=
  match switch_list with
  | [] => (List.ofFn (fun _ : Fin (2 * n) => false))
  | h :: t => switch_lamp n h (lamps_final_state n t)

def final_goal (n : ℕ+) := List.ofFn (fun (i : Fin (2 * n)) => if i.val < n then true else false)

def N (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => lamps_final_state n (List.ofFn f) = final_goal n) |>.card

def M (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => ∀ (i : Fin k), f i < ⟨n.1, lt_two_mul_self n.2⟩) |>.filter
  (fun f => lamps_final_state n (List.ofFn f) = final_goal n) |>.card

noncomputable abbrev imo_2008_p5_solution : ℕ+ → ℕ+ → ℝ := fun n k => 2 ^ (k.1 - n.1)
lemma A (n:ℕ+) : ∀ (k:ℕ) (f : Fin k → Fin (2*n)), lamps_final_state n (List.ofFn f) = List.ofFn (fun i : Fin (2*n) => decide (Odd (∑ j, if f j = i then 1 else 0))) := by
  intro k
  induction k with
  | zero => intro f; simp [lamps_final_state]
  | succ k ih =>
    intro f
    rw [List.ofFn_succ]
    simp only [lamps_final_state]
    rw [ih]
    apply List.ext_getElem
    · simp [switch_lamp]
    · intro i h1 h2
      simp only [switch_lamp, List.getElem_mapIdx, List.getElem_ofFn]
      rw [Fin.sum_univ_succ]
      generalize (∑ j : Fin k, if f j.succ = (⟨i, by simpa using h2⟩ : Fin (2*n)) then 1 else 0) = s
      by_cases h : f 0 = ⟨i, by simpa using h2⟩
      · have h' : i = ((f 0 : Fin (2*n)) : ℕ) := by rw [h]
        rw [if_pos h', if_pos h]
        cases hs : Nat.even_or_odd s with
        | inl he => simp [Nat.odd_add, he, Nat.not_odd_iff_even.mpr he]
        | inr ho => simp [Nat.odd_add, ho, Nat.not_even_iff_odd.mpr ho]
      · have h' : ¬ i = ((f 0 : Fin (2*n)) : ℕ) := fun e => h (Fin.ext e.symm)
        rw [if_neg h', if_neg h]
        simp
lemma W {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : Fin k → ι) (hg : Function.Surjective g) :
    (Finset.univ.filter (fun b : Fin k → Bool => ∀ i, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))).card * 2^(Fintype.card ι) = 2^k := by
  classical
  let par : (Fin k → Bool) → ι → Bool := fun b i => decide (Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))
  have h1 : 2^k = ∑ t : ι → Bool, (Finset.univ.filter (fun b => par b = t)).card := by
    have := Finset.card_eq_sum_card_fiberwise (f := par) (s := (Finset.univ : Finset (Fin k → Bool))) (t := (Finset.univ : Finset (ι → Bool))) (fun _ _ => Finset.mem_univ _)
    simpa using this
  let p : ι → Fin k := Function.surjInv hg
  have hp : ∀ i, g (p i) = i := fun i => Function.surjInv_eq hg i
  have key : ∀ (t : ι → Bool) (b : Fin k → Bool) (i : ι),
      par (fun j => xor (b j) (decide (p (g j) = j) && t (g j))) i = xor (par b i) (t i) := by
    intro t b i
    have hE : (∑ j, if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = if t i = true then 1 else 0 := by
      have : ∀ j, (if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = if j = p i then (if t i = true then 1 else 0) else 0 := by
        intro j
        by_cases hj : j = p i
        · subst hj
          simp [hp]
        · have : ¬ (g j = i ∧ (decide (p (g j) = j) && t (g j)) = true) := by
            rintro ⟨h1, h2⟩
            simp at h2
            apply hj
            rw [← h1]; exact h2.1.symm
          rw [if_neg this, if_neg hj]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
    have hsum : (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0)
        + 2 * (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0)
        = (∑ j, if g j = i ∧ b j = true then 1 else 0) + (∑ j, if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases hb : b j <;> cases he : (decide (p (g j) = j) && t (g j)) <;> by_cases hgi : g j = i <;> simp [hb, he, hgi]
    rw [hE] at hsum
    simp only [par]
    by_cases ht : t i = true
    · rw [if_pos ht] at hsum
      simp only [ht]
      generalize (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0) = a' at hsum ⊢
      generalize (∑ j, if g j = i ∧ b j = true then 1 else 0) = a at hsum ⊢
      generalize (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = X at hsum
      simp only [Nat.odd_iff]
      by_cases h : a % 2 = 1 <;> by_cases h' : a' % 2 = 1 <;> simp [h, h'] <;> omega
    · rw [if_neg ht] at hsum
      have : t i = false := by simpa using ht
      simp only [this]
      generalize (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0) = a' at hsum ⊢
      generalize (∑ j, if g j = i ∧ b j = true then 1 else 0) = a at hsum ⊢
      generalize (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = X at hsum
      simp only [Nat.odd_iff]
      by_cases h : a % 2 = 1 <;> by_cases h' : a' % 2 = 1 <;> simp [h, h'] <;> omega
  have h2 : ∀ t : ι → Bool, (Finset.univ.filter (fun b => par b = t)).card = (Finset.univ.filter (fun b => par b = fun _ => false)).card := by
    intro t
    apply Finset.card_nbij' (fun b j => xor (b j) (decide (p (g j) = j) && t (g j))) (fun b j => xor (b j) (decide (p (g j) = j) && t (g j)))
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      funext i
      rw [key, congrFun hb i]
      cases t i <;> rfl
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      funext i
      rw [key, congrFun hb i]
      cases t i <;> rfl
    · intro b _
      funext j
      show (xor (xor (b j) (decide (p (g j) = j) && t (g j))) (decide (p (g j) = j) && t (g j))) = b j
      generalize b j = x
      generalize (decide (p (g j) = j) && t (g j)) = y
      cases x <;> cases y <;> rfl
    · intro b _
      funext j
      show (xor (xor (b j) (decide (p (g j) = j) && t (g j))) (decide (p (g j) = j) && t (g j))) = b j
      generalize b j = x
      generalize (decide (p (g j) = j) && t (g j)) = y
      cases x <;> cases y <;> rfl
  have h3 : (Finset.univ.filter (fun b : Fin k → Bool => ∀ i, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))) = Finset.univ.filter (fun b => par b = fun _ => false) := by
    ext b
    simp [par, funext_iff]
  rw [h3]
  rw [h1, Finset.sum_congr rfl (fun t _ => h2 t)]
  simp [mul_comm]
lemma Rl (n k : ℕ+) (f : Fin k → Fin (2*n)) (g : Fin k → Fin n) (b : Fin k → Bool)
    (hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((g j : Fin n) : ℕ) + if b j = true then (n:ℕ) else 0) (i : Fin n) :
    (∑ j, if f j = (⟨i.val, by have := i.isLt; omega⟩ : Fin (2*n)) then 1 else 0) = (∑ j, if g j = i ∧ b j = false then 1 else 0) ∧
    (∑ j, if f j = (⟨i.val + n, by have := i.isLt; omega⟩ : Fin (2*n)) then 1 else 0) = (∑ j, if g j = i ∧ b j = true then 1 else 0) ∧
    (∑ j, if g j = i then 1 else 0) = (∑ j, if g j = i ∧ b j = false then 1 else 0) + (∑ j, if g j = i ∧ b j = true then 1 else 0) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sum_congr rfl
    intro j _
    have h := hR j
    have e : (f j = (⟨i.val, by omega⟩ : Fin (2*n))) ↔ (g j = i ∧ b j = false) := by
      rw [Fin.ext_iff, Fin.ext_iff]
      cases hb : b j <;> simp [hb] at h ⊢ <;> omega
    exact if_congr e rfl rfl
  · apply Finset.sum_congr rfl
    intro j _
    have h := hR j
    have e : (f j = (⟨i.val + n, by omega⟩ : Fin (2*n))) ↔ (g j = i ∧ b j = true) := by
      rw [Fin.ext_iff, Fin.ext_iff]
      cases hb : b j <;> simp [hb] at h ⊢ <;> omega
    exact if_congr e rfl rfl
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    cases hb : b j <;> by_cases hg : g j = i <;> simp [hb, hg]
lemma memEq (n k : ℕ+) (f : Fin k → Fin (2*n)) (g : Fin k → Fin n) (b : Fin k → Bool)
    (hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((g j : Fin n) : ℕ) + if b j = true then (n:ℕ) else 0) :
    (∀ x : Fin (2*n), Odd (∑ j, if f j = x then 1 else 0) ↔ x.val < n) ↔
    ((∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0)) ∧ ∀ i : Fin n, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0)) := by
  have hl1 : ∀ i : Fin n, i.val < 2*n := fun i => by have := i.isLt; omega
  have hl2 : ∀ i : Fin n, i.val + n < 2*n := fun i => by have := i.isLt; omega
  constructor
  · intro h
    constructor
    · intro i
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      have h1 := (h ⟨i.val, by have := i.isLt; omega⟩).2 i.isLt
      have h2 := h ⟨i.val + n, by have := i.isLt; omega⟩
      simp only [ha] at h1
      simp only [hb] at h2
      have h3 : ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0) := by
        intro ho; have := h2.1 ho; omega
      rw [hc]
      simp only [Nat.odd_iff] at h1 h3 ⊢
      omega
    · intro i
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      have h2 := h ⟨i.val + n, by have := i.isLt; omega⟩
      simp only [hb] at h2
      intro ho; have := h2.1 ho; omega
  · rintro ⟨h1, h2⟩ x
    by_cases hx : x.val < n
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, x = ⟨i.val, hl1 i⟩ := ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
      subst hi
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      simp only [ha]
      have a1 := h1 i
      have a2 := h2 i
      rw [hc] at a1
      simp only [Nat.odd_iff] at a1 a2 ⊢
      simp only [i.isLt, iff_true]
      omega
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, x = ⟨i.val + n, hl2 i⟩ := ⟨⟨x.val - n, by have := x.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      subst hi
      obtain ⟨ha, hb, hc⟩ := Rl n k f g b hR i
      simp only [hb]
      simp only [Fin.val_mk] at hx ⊢
      simp only [hx, iff_false]
      exact h2 i
lemma Bc (n : ℕ+) (k : ℕ) (f : Fin k → Fin (2*n)) : lamps_final_state n (List.ofFn f) = final_goal n ↔ ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n := by
  rw [A, final_goal, List.ofFn_inj, funext_iff]
  simp

lemma Cc (n : ℕ+) (k : ℕ) (g : Fin k → Fin n) (i : Fin (2*n)) :
    (∑ j, if (Fin.castLE (by omega : (n:ℕ) ≤ 2 * n) (g j)) = i then 1 else 0) = if h : i.val < n then ∑ j, if g j = ⟨i, h⟩ then 1 else 0 else 0 := by
  by_cases h : i.val < n
  · rw [dif_pos h]
    apply Finset.sum_congr rfl
    intro j _
    exact if_congr (by simp [Fin.ext_iff]) rfl rfl
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have := (g j).isLt
    rw [if_neg]
    intro e
    rw [← e] at h
    simp at h
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
lemma mainN (n k : ℕ+) (hk : (n:ℕ) ≤ k) (hex : ∃ g : Fin k → Fin n, ∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0)) :
    N n k = 2^((k:ℕ)-n) * M n k ∧ 0 < M n k := by
  classical
  have hn := n.pos
  have h2n : (n:ℕ) ≤ 2 * n := by omega
  let G : Finset (Fin k → Fin n) := Finset.univ.filter (fun g => ∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0))
  let Bs : (Fin k → Fin n) → Finset (Fin k → Bool) := fun g =>
    Finset.univ.filter (fun b : Fin k → Bool => ∀ i : Fin n, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))
  have hN1 : N n k = (Finset.univ.filter (fun f : Fin k → Fin (2*n) => ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card := by
    unfold N
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Bc n k f
  have hM1 : M n k = (Finset.univ.filter (fun f : Fin k → Fin (2*n) => (∀ j, (f j).val < n) ∧ ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card := by
    unfold M
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Bc n k f]
    exact Iff.rfl
  have hMG : M n k = G.card := by
    rw [hM1]
    symm
    apply Finset.card_bij (fun g _ => fun j => Fin.castLE h2n (g j))
    · intro g hg
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun j => (g j).isLt, fun i => ?_⟩
      rw [Cc]
      by_cases h : i.val < n
      · rw [dif_pos h]; simpa [h] using hg ⟨i, h⟩
      · rw [dif_neg h]; simp [h]
    · intro g _ g' _ e
      funext j
      exact Fin.castLE_injective h2n (congrFun e j)
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨hlt, hodd⟩ := hf
      refine ⟨fun j => ⟨(f j).val, hlt j⟩, ?_, ?_⟩
      · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        have := (hodd (Fin.castLE h2n i)).2 (by simp)
        have e : (∑ x, if (⟨(f x).val, hlt x⟩ : Fin n) = i then 1 else 0) = ∑ j, if f j = Fin.castLE h2n i then 1 else 0 :=
          Finset.sum_congr rfl (fun j _ => if_congr (by rw [Fin.ext_iff, Fin.ext_iff]; simp [eq_comm]) rfl rfl)
        rw [e]; exact this
      · funext j; exact Fin.ext rfl
  have hmod : ∀ v : ℕ, v < 2 * n → v % n = if (n:ℕ) ≤ v then v - n else v := by
    intro v hv
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hcard : (Finset.univ.filter (fun f : Fin k → Fin (2*n) => ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card = (G.sigma Bs).card := by
    refine Finset.card_nbij' (fun f => (⟨fun j => ⟨(f j).val % n, Nat.mod_lt _ hn⟩, fun j => decide ((n:ℕ) ≤ (f j).val)⟩ : Σ _ : Fin k → Fin n, Fin k → Bool))
      (fun x => fun j => ⟨(x.1 j).val + if x.2 j = true then (n:ℕ) else 0, by have := (x.1 j).isLt; split_ifs <;> omega⟩) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      have hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((⟨(f j).val % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ) + if decide ((n:ℕ) ≤ (f j).val) = true then (n:ℕ) else 0 := by
        intro j
        have := (f j).isLt
        simp only [hmod _ this, decide_eq_true_eq]
        split_ifs <;> omega
      have := (memEq n k f _ _ hR).1 hf
      simp only [Finset.mem_coe, Finset.mem_sigma, G, Bs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact this
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_sigma, G, Bs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (memEq n k _ x.1 x.2 (fun j => rfl)).2 hx
    · intro f _
      funext j
      apply Fin.ext
      have := (f j).isLt
      simp only [hmod _ this, decide_eq_true_eq]
      split_ifs <;> omega
    · rintro ⟨g, b⟩ _
      refine Sigma.ext ?_ (heq_of_eq ?_)
      · funext j
        apply Fin.ext
        have := (g j).isLt
        show ((g j).val + if b j = true then (n:ℕ) else 0) % n = (g j).val
        split_ifs
        · rw [Nat.add_mod_right, Nat.mod_eq_of_lt this]
        · rw [Nat.add_zero, Nat.mod_eq_of_lt this]
      · funext j
        have := (g j).isLt
        show decide ((n:ℕ) ≤ (g j).val + if b j = true then (n:ℕ) else 0) = b j
        cases hb : b j <;> simp <;> omega
  have hBs : ∀ g ∈ G, (Bs g).card = 2^((k:ℕ) - n) := by
    intro g hg
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have hsurj : Function.Surjective g := by
      intro i
      have := hg i
      by_contra hne
      push_neg at hne
      have h0 : (∑ j, if g j = i then 1 else 0) = 0 := Finset.sum_eq_zero (fun j _ => if_neg (hne j))
      rw [h0] at this
      simp at this
    have := W (ι := Fin n) k g hsurj
    simp only [Fintype.card_fin] at this
    have h3 : (2:ℕ)^(k:ℕ) = 2^((k:ℕ) - n) * 2^(n:ℕ) := by rw [← pow_add]; congr 1; omega
    rw [h3] at this
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0:ℕ) < 2) (n:ℕ)) (by convert this)
  refine ⟨?_, ?_⟩
  · rw [hN1, hcard, Finset.card_sigma, Finset.sum_congr rfl hBs, hMG]
    simp [mul_comm]
  · rw [hMG]
    obtain ⟨g, hg⟩ := hex
    exact Finset.card_pos.2 ⟨g, by simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]; exact hg⟩
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
