import Mathlib

open Set Nat

/--
Suppose that a finite group has exactly $n$ elements of order $p$, where $p$ is a prime. Prove that either $n = 0$ or $p$ divides $n+1$.
-/
theorem putnam_2007_a5
(G : Type*) [Group G] [Fintype G]
(p n : ℕ)
(hp : Nat.Prime p)
(hn : n = {g : G | orderOf g = p}.encard)
: n = 0 ∨ p ∣ (n + 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have frob : ∀ k : ℕ, Nat.Prime (k+1) → (k+1) ∣ Fintype.card G →
      (k+1) ∣ Nat.card {g : G // g^(k+1) = 1} := by
    intro k hk hd
    have : Fact (k+1).Prime := ⟨hk⟩
    classical
    have : Fact (k+1).Prime := ⟨hk⟩
    have hpos : 0 < k + 1 := Nat.succ_pos k
    have hk0 : k ≠ 0 := by have := hk.one_lt; omega
    have hrot : ∀ x : Fin (k+1) → G,
        (List.ofFn (fun i : Fin (k+1) => x ⟨(i.val+1) % (k+1), Nat.mod_lt _ hpos⟩))
          = (List.ofFn x).rotate 1 := by
      intro x
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_rotate]
      · intro n h1 h2
        simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
    let r : {x : Fin (k+1) → G // (List.ofFn x).prod = 1} → {x : Fin (k+1) → G // (List.ofFn x).prod = 1} :=
      fun x => ⟨fun i => x.1 ⟨(i.val+1) % (k+1), Nat.mod_lt _ hpos⟩, by
        rw [hrot]; exact List.prod_rotate_eq_one_of_prod_eq_one x.2 1⟩
    have hiter : ∀ m (x : {x : Fin (k+1) → G // (List.ofFn x).prod = 1}) (i : Fin (k+1)),
        (r^[m] x).1 i = x.1 ⟨(i.val+m) % (k+1), Nat.mod_lt _ hpos⟩ := by
      intro m
      induction m with
      | zero =>
        intro x i
        refine congrArg (fun j => x.1 j) (Fin.ext ?_)
        simp [Nat.mod_eq_of_lt i.isLt]
      | succ m ih =>
        intro x i
        rw [Function.iterate_succ_apply']
        show (r^[m] x).1 ⟨(i.val+1) % (k+1), _⟩ = _
        rw [ih]
        refine congrArg (fun j => x.1 j) (Fin.ext ?_)
        dsimp only
        rw [Nat.mod_add_mod]
        congr 1
        omega
    let f : Function.End {x : Fin (k+1) → G // (List.ofFn x).prod = 1} := r
    have hf : f^((k+1)^1) = 1 := by
      funext x
      apply Subtype.ext
      funext i
      change (r^[(k+1)^1] x).1 i = x.1 i
      rw [hiter]
      refine congrArg (fun j => x.1 j) (Fin.ext ?_)
      show (i.val + (k+1)^1) % (k+1) = i.val
      rw [pow_one, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := k+1) (n := 1) hf
    -- fixed points are constant
    have hconst : ∀ x : {x : Fin (k+1) → G // (List.ofFn x).prod = 1}, r x = x →
        ∀ i : Fin (k+1), x.1 i = x.1 0 := by
      intro x hx
      have hstep : ∀ i : Fin (k+1), x.1 ⟨(i.val+1) % (k+1), Nat.mod_lt _ hpos⟩ = x.1 i :=
        fun i => congrArg (fun y : {x : Fin (k+1) → G // (List.ofFn x).prod = 1} => y.1 i) hx
      have h1 : ∀ j (hj : j < k+1), x.1 ⟨j, hj⟩ = x.1 0 := by
        intro j
        induction j with
        | zero => intro hj; rfl
        | succ j ih =>
          intro hj
          have e : x.1 ⟨(j+1) % (k+1), Nat.mod_lt _ hpos⟩ = x.1 ⟨j+1, hj⟩ :=
            congrArg x.1 (Fin.ext (Nat.mod_eq_of_lt hj))
          rw [← e]
          exact (hstep ⟨j, by omega⟩).trans (ih (by omega))
      intro i
      exact h1 i.val i.isLt
    have hpowof : ∀ x : {x : Fin (k+1) → G // (List.ofFn x).prod = 1}, r x = x → (x.1 0)^(k+1) = 1 := by
      intro x hx
      have hc : x.1 = fun _ => x.1 0 := funext (hconst x hx)
      have h := x.2
      rw [hc, List.ofFn_const, List.prod_replicate] at h
      exact h
    -- equivalence with fixed points
    let E : {g : G // g^(k+1) = 1} ≃ ↥(Function.fixedPoints f) :=
      { toFun := fun g => ⟨⟨fun _ => g.1, by
            rw [List.ofFn_const, List.prod_replicate]; exact g.2⟩, by
            show r _ = _
            apply Subtype.ext
            rfl⟩
        invFun := fun x => ⟨x.1.1 0, hpowof x.1 x.2⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun x => Subtype.ext (Subtype.ext (funext fun i => (hconst x.1 x.2 i).symm)) }
    have hfix : Nat.card (Function.fixedPoints f) = Nat.card {g : G // g^(k+1) = 1} :=
      (Nat.card_congr E).symm
    -- cardinality of the tuple set
    let EΩ : {x : Fin (k+1) → G // (List.ofFn x).prod = 1} ≃ (Fin k → G) :=
      { toFun := fun x i => x.1 i.castSucc
        invFun := fun y => ⟨Fin.snoc (α := fun _ => G) y ((List.ofFn y).prod)⁻¹, by
            rw [List.ofFn_succ']
            simp⟩
        left_inv := by
          intro x
          apply Subtype.ext
          funext i
          induction i using Fin.lastCases with
          | last =>
            have h := x.2
            rw [List.ofFn_succ'] at h
            simp only [List.concat_eq_append, List.prod_append, List.prod_singleton] at h
            simp only [Fin.snoc_last]
            exact (eq_inv_of_mul_eq_one_right h).symm
          | cast j => simp [Fin.snoc_castSucc]
        right_inv := by
          intro y
          funext i
          simp [Fin.snoc_castSucc] }
    have hcard : Nat.card {x : Fin (k+1) → G // (List.ofFn x).prod = 1} = Nat.card G ^ k := by
      rw [Nat.card_congr EΩ]
      simp [Nat.card_eq_fintype_card]
    have h0 : Nat.card {x : Fin (k+1) → G // (List.ofFn x).prod = 1} ≡ 0 [MOD k+1] := by
      apply Nat.modEq_zero_iff_dvd.2
      rw [hcard]
      exact dvd_pow (by rw [Nat.card_eq_fintype_card]; exact hd) hk0
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
    rw [← hfix]
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans h0)
  set S : Set G := {g : G | orderOf g = k+1} with hSdef
  have hT : ({g : G | g^(k+1) = 1} : Set G) = insert 1 S := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, hSdef]
    constructor
    · intro h
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_iff_pow_eq_one.2 h) with h1 | h1
      · left; exact orderOf_eq_one_iff.1 h1
      · right; exact h1
    · rintro (rfl | h)
      · simp
      · exact orderOf_dvd_iff_pow_eq_one.1 (h ▸ dvd_refl _)
  have h1S : (1 : G) ∉ S := by
    intro h
    have : orderOf (1 : G) = 1 := orderOf_one
    simp only [hSdef, Set.mem_ofPred_eq] at h
    rw [this] at h
    have := hp.one_lt
    omega
  have hScard : S.ncard = n := by
    have : (S.ncard : ℕ∞) = (n : ℕ∞) := by
      rw [hn]; exact Set.Finite.cast_ncard_eq (Set.toFinite _)
    exact_mod_cast this
  have hTn : Nat.card {g : G // g^(k+1) = 1} = n + 1 := by
    rw [show Nat.card {g : G // g^(k+1) = 1} = ({g : G | g^(k+1) = 1} : Set G).ncard from
      (Nat.card_coe_set_eq _).symm, hT, Set.ncard_insert_of_notMem h1S, hScard]
  by_cases h0 : n = 0
  · exact Or.inl h0
  · right
    have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hScard]; exact h0)
    obtain ⟨g, hg⟩ := hne
    have hdvd : k + 1 ∣ Fintype.card G := by
      rw [← hg]
      exact orderOf_dvd_card
    rw [← hTn]
    exact frob k hp hdvd
