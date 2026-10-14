import Mathlib

open Nat Topology Filter

-- Note: uses (ℕ → Fin n → ℝ) instead of (Fin N → Fin n → ℝ)
/--
Show that for any positive integer $n$ there is an integer $N$ such that the product $x_1x_2 \cdots x_n$ can be expressed identically in the form $x_1x_2 \cdots x_n=\sum_{i=1}^Nc_i(a_{i1}x_1+a_{i2}x_2+\cdots+a_{in}x_n)^n$ where the $c_i$ are rational numbers and each $a_{ij}$ is one of the numbers $-1,0,1$.
-/
theorem putnam_2004_a4
  (n : ℕ) (npos : n > 0)
  (x : Fin n → ℝ)
  (avals : ℕ → (ℕ → Fin n → ℝ) → Prop)
  (havals : ∀ N a, avals N a ↔ ∀ (i : Fin N) (j : Fin n), (a i j = -1 ∨ a i j = 0 ∨ a i j = 1)) :
  ∃ (N : ℕ) (c : Fin N → ℚ) (a : ℕ → Fin n → ℝ),
    avals N a ∧
    (∏ i : Fin n, x i) = ∑ i : Fin N, c i * (∑ j : Fin n, a i j * x j) ^ n :=
by
  obtain ⟨s, hs⟩ : ∃ s : Bool → ℝ, ∀ b, s b = if b then 1 else -1 :=
    ⟨fun b => if b then 1 else -1, fun b => rfl⟩
  have hbij : ∀ f : Fin n → Fin n,
      (∀ j, Odd ((Finset.univ.filter (fun k => f k = j)).card)) ↔ Function.Bijective f := by
    intro f
    constructor
    · intro h
      have hsurj : Function.Surjective f := by
        intro j
        obtain ⟨k, hk⟩ := Finset.card_pos.mp (h j).pos
        exact ⟨k, (Finset.mem_filter.1 hk).2⟩
      exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    · rintro ⟨hinj, hsurj⟩ j
      obtain ⟨k, hk⟩ := hsurj j
      have hc : (Finset.univ.filter (fun k => f k = j)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨k, ?_⟩
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hm; exact hinj (hm.trans hk.symm)
        · rintro rfl; exact hk
      rw [hc]; exact odd_one
  have hinner : ∀ f : Fin n → Fin n,
      (∑ ε : Fin n → Bool, (∏ j, s (ε j)) * ∏ k, s (ε (f k))) =
        if (∀ j, Odd ((Finset.univ.filter (fun k => f k = j)).card)) then (2:ℝ)^n else 0 := by
    intro f
    have h1 : ∀ ε : Fin n → Bool, (∏ j, s (ε j)) * ∏ k, s (ε (f k)) =
        ∏ j, s (ε j) ^ ((Finset.univ.filter (fun k => f k = j)).card + 1) := by
      intro ε
      rw [← Finset.prod_fiberwise Finset.univ f (fun k => s (ε (f k)))]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have h2 : ∏ k ∈ Finset.univ.filter (fun k => f k = j), s (ε (f k))
          = s (ε j) ^ (Finset.univ.filter (fun k => f k = j)).card := by
        rw [Finset.prod_congr rfl (g := fun _ => s (ε j))
          (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.prod_const]
      rw [h2]; ring
    have h3 : ∀ m : Fin n → ℕ, (∑ ε : Fin n → Bool, ∏ j, s (ε j) ^ m j) =
        ∏ j, (s true ^ m j + s false ^ m j) := by
      intro m
      calc (∑ ε : Fin n → Bool, ∏ j, s (ε j) ^ m j)
          = ∑ x : (∀ _j : Fin n, Bool), ∏ j, (fun (j : Fin n) (b : Bool) => s b ^ m j) j (x j) := rfl
        _ = ∏ j, ∑ b : Bool, s b ^ m j := (Fintype.prod_sum (fun (j : Fin n) (b : Bool) => s b ^ m j)).symm
        _ = ∏ j, (s true ^ m j + s false ^ m j) := by simp
    simp only [h1]
    rw [h3 (fun j => (Finset.univ.filter (fun k => f k = j)).card + 1)]
    by_cases h : ∀ j, Odd ((Finset.univ.filter (fun k => f k = j)).card)
    · rw [if_pos h]
      have hfac : ∀ j, s true ^ ((Finset.univ.filter (fun k => f k = j)).card + 1)
          + s false ^ ((Finset.univ.filter (fun k => f k = j)).card + 1) = 2 := by
        intro j
        rw [hs true, hs false]
        simp only [if_true, Bool.false_eq_true, if_false]
        rw [one_pow, Even.neg_one_pow (h j).add_one]; norm_num
      rw [Finset.prod_congr rfl (fun j _ => hfac j)]
      simp
    · rw [if_neg h]
      push_neg at h
      obtain ⟨j, hj⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hs true, hs false]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [Odd.neg_one_pow (Nat.not_odd_iff_even.mp hj).add_one]; norm_num
  have key : ∑ ε : Fin n → Bool, (∏ j, s (ε j)) * (∑ j, s (ε j) * x j) ^ n
      = (2:ℝ)^n * (n.factorial : ℝ) * ∏ j, x j := by
    have hpow : ∀ ε : Fin n → Bool, (∑ j, s (ε j) * x j) ^ n
        = ∑ f : Fin n → Fin n, ∏ k, s (ε (f k)) * x (f k) := by
      intro ε
      calc (∑ j, s (ε j) * x j) ^ n = ∏ _k : Fin n, ∑ j, s (ε j) * x j := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = ∑ f : Fin n → Fin n, ∏ k, s (ε (f k)) * x (f k) :=
            Fintype.prod_sum (fun _ j => s (ε j) * x j)
    calc ∑ ε : Fin n → Bool, (∏ j, s (ε j)) * (∑ j, s (ε j) * x j) ^ n
        = ∑ ε : Fin n → Bool, ∑ f : Fin n → Fin n, (∏ j, s (ε j)) * ∏ k, s (ε (f k)) * x (f k) := by
          apply Finset.sum_congr rfl; intro ε _; rw [hpow ε, Finset.mul_sum]
      _ = ∑ f : Fin n → Fin n, ∑ ε : Fin n → Bool, (∏ j, s (ε j)) * ∏ k, s (ε (f k)) * x (f k) :=
          Finset.sum_comm
      _ = ∑ f : Fin n → Fin n, (∏ k, x (f k)) *
            (∑ ε : Fin n → Bool, (∏ j, s (ε j)) * ∏ k, s (ε (f k))) := by
          apply Finset.sum_congr rfl; intro f _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ε _
          rw [Finset.prod_mul_distrib]; ring
      _ = ∑ f : Fin n → Fin n, (∏ k, x (f k)) *
            (if (∀ j, Odd ((Finset.univ.filter (fun k => f k = j)).card)) then (2:ℝ)^n else 0) := by
          apply Finset.sum_congr rfl; intro f _; rw [hinner f]
      _ = ∑ f : Fin n → Fin n, if Function.Bijective f then (2:ℝ)^n * ∏ k, x (f k) else 0 := by
          apply Finset.sum_congr rfl; intro f _
          by_cases h : (∀ j, Odd ((Finset.univ.filter (fun k => f k = j)).card))
          · rw [if_pos h, if_pos ((hbij f).mp h)]; ring
          · rw [if_neg h, if_neg (fun hb => h ((hbij f).mpr hb))]; ring
      _ = ∑ σ : Equiv.Perm (Fin n), (2:ℝ)^n * ∏ k, x (σ k) := by
          symm
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
            (t := Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f))
            (fun σ _ => ((σ : Equiv.Perm (Fin n)) : Fin n → Fin n)) ?_ ?_ ?_ ?_
          · intro σ _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.bijective⟩
          · intro a _ b _ h; exact Equiv.ext (fun y => congrFun h y)
          · intro f hf; exact ⟨Equiv.ofBijective f (Finset.mem_filter.1 hf).2, Finset.mem_univ _, rfl⟩
          · intro σ _; rfl
      _ = (2:ℝ)^n * (n.factorial : ℝ) * ∏ j, x j := by
          have hperm : ∀ σ : Equiv.Perm (Fin n), (2:ℝ)^n * ∏ k, x (σ k) = (2:ℝ)^n * ∏ k, x k :=
            fun σ => by rw [Equiv.prod_comp σ x]
          rw [Finset.sum_congr rfl (fun σ _ => hperm σ), Finset.sum_const, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  let e := Fintype.equivFin (Fin n → Bool)
  refine ⟨Fintype.card (Fin n → Bool),
    fun i => ((∏ j, (if e.symm i j then 1 else -1 : ℚ)) / (2^n * (n.factorial : ℚ))),
    fun i j => if h : i < Fintype.card (Fin n → Bool) then s (e.symm ⟨i, h⟩ j) else 0, ?_, ?_⟩
  · rw [havals]
    intro i j
    rw [dif_pos i.isLt, hs]
    split_ifs <;> norm_num
  · symm
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans
      ((Equiv.sum_comp e.symm (fun ε : Fin n → Bool =>
        (∏ j, s (ε j)) / (2^n * (n.factorial : ℝ)) * (∑ j, s (ε j) * x j) ^ n)).trans ?_)
    · have hi : (i : ℕ) < Fintype.card (Fin n → Bool) := i.isLt
      simp only [hi, dite_true, Fin.eta, hs]
      push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
      ring
    · have hsplit : ∑ ε : Fin n → Bool, (∏ j, s (ε j)) / (2^n * (n.factorial : ℝ)) * (∑ j, s (ε j) * x j) ^ n
          = ((2:ℝ)^n * (n.factorial : ℝ))⁻¹ * ∑ ε : Fin n → Bool, (∏ j, s (ε j)) * (∑ j, s (ε j) * x j) ^ n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ε _; ring
      rw [hsplit, key]
      field_simp
