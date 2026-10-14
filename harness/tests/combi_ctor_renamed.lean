import Mathlib

structure Boxes where
  (B1 B2 B3 B4 B5 B6 : ℕ)

def op11 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1 - 1, b2 + 2, b3, b4, b5, b6⟩

def op12 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2 - 1, b3 + 2, b4, b5, b6⟩

def op13 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3 - 1, b4 + 2, b5, b6⟩

def op14 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4 - 1, b5 + 2, b6⟩

def op15 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4, b5 - 1, b6 + 2⟩

def op21 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1 - 1, b3, b2, b4, b5, b6⟩

def op22 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2 - 1, b4, b3, b5, b6⟩

def op23 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3 - 1, b5, b4, b6⟩

def op24 : Boxes → Boxes
  | ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4 - 1, b6, b5⟩

inductive OP
  | op11 | op12 | op13 | op14 | op15 | op21 | op22 | op23 | op25

def apply_op : OP → (Boxes → Boxes)
  | OP.op11 => op11
  | OP.op12 => op12
  | OP.op13 => op13
  | OP.op14 => op14
  | OP.op15 => op15
  | OP.op21 => op21
  | OP.op22 => op22
  | OP.op23 => op23
  | OP.op25 => op24

def init : Boxes := ⟨1, 1, 1, 1, 1, 1⟩

noncomputable abbrev imo_2010_p5_solution : Bool := true

/--
Each of the six boxes $B_1$, $B_2$, $B_3$, $B_4$, $B_5$, $B_6$ initially contains one coin. The following operations are allowed: Type 1) Choose a non-empty box $B_j$, $1\leq j \leq 5$, remove one coin from $B_j$ and add two coins to $B_{j+1}$; Type 2) Choose a non-empty box $B_k$, $1\leq k \leq 4$, remove one coin from $B_k$ and swap the contents (maybe empty) of the boxes $B_{k+1}$ and $B_{k+2}$. Determine if there exists a finite sequence of operations of the allowed types, such that the five boxes $B_1$, $B_2$, $B_3$, $B_4$, $B_5$ become empty, while box $B_6$ contains exactly $2010^{2010^{2010}}$ coins.
-/
theorem imo_2010_p5 : imo_2010_p5_solution = (∃ seq : List OP,
    (seq.map apply_op).foldl (· ∘ ·) id init = ⟨0, 0, 0, 0, 0, 2010 ^ (2010 ^ 2010)⟩) := 
by
  have hF : ∀ (l : List OP) (a : Boxes → Boxes),
      (l.map apply_op).foldl (· ∘ ·) a = a ∘ (l.map apply_op).foldl (· ∘ ·) id := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x l ih =>
      intro a
      simp only [List.map_cons, List.foldl_cons]
      rw [ih, ih (id ∘ _)]
      rfl
  have hApp : ∀ l1 l2 : List OP, ((l1 ++ l2).map apply_op).foldl (· ∘ ·) id =
      ((l1.map apply_op).foldl (· ∘ ·) id) ∘ ((l2.map apply_op).foldl (· ∘ ·) id) := by
    intro l1 l2
    rw [List.map_append, List.foldl_append, hF]
  have hRep : ∀ (n : ℕ) (c : ℕ), ((List.replicate n OP.op15).map apply_op).foldl (· ∘ ·) id
      ⟨0, 0, 0, 0, 0, c⟩ = ⟨0, 0, 0, 0, 0, c + 2 * n⟩ := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      rw [List.replicate_succ', hApp]
      have : (([OP.op15].map apply_op).foldl (· ∘ ·) id) ⟨0, 0, 0, 0, 0, c⟩ = ⟨0,0,0,0,0,c+2⟩ := rfl
      simp only [Function.comp, this, ih]
      show (⟨0, 0, 0, 0, 0, c + 2 + 2 * n⟩ : Boxes) = _
      congr 1; omega
  have key : ∀ M : ℕ, 0 < M → 2 ∣ 2010 ^ M ∧ 36 ≤ 2010 ^ M := by
    intro M hM
    refine ⟨dvd_pow (by norm_num : 2 ∣ 2010) hM.ne', ?_⟩
    calc 36 ≤ 2010 ^ 1 := by norm_num
      _ ≤ 2010 ^ M := Nat.pow_le_pow_right (by norm_num) hM
  have hM : 0 < 2010 ^ 2010 := by positivity
  obtain ⟨hEven, hBig⟩ := key _ hM
  generalize 2010 ^ (2010 ^ 2010) = N at hEven hBig ⊢
  obtain ⟨n, hn⟩ : ∃ n, N = 36 + 2 * n := by
    obtain ⟨k, hk⟩ := hEven
    exact ⟨k - 18, by omega⟩
  let ex : List OP := [OP.op11, OP.op12, OP.op21, OP.op22, OP.op23, OP.op25,
    OP.op12, OP.op12, OP.op13, OP.op13, OP.op13, OP.op13] ++ List.replicate 8 OP.op14
    ++ List.replicate 17 OP.op15
  have h0 : ((ex.reverse.map apply_op).foldl (· ∘ ·) id) init = ⟨0, 0, 0, 0, 0, 36⟩ := by
    rfl
  refine propext (iff_of_true rfl ?_)
  refine ⟨List.replicate n OP.op15 ++ ex.reverse, ?_⟩
  rw [hApp]
  simp only [Function.comp, h0, hRep, hn]
