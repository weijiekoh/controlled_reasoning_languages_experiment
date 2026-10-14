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
  have : Fact (k+1).Prime := ⟨hp⟩
  have hk : k ≠ 0 := by
    intro h; subst h; exact Nat.not_prime_one hp
  set S : Finset G := Finset.univ.filter (fun g : G => orderOf g = k + 1) with hS
  have hnS : n = S.card := by
    have : {g : G | orderOf g = k+1} = ((S : Finset G) : Set G) := by
      ext g; simp [hS]
    rw [this, Set.encard_coe_eq_coe_finsetCard] at hn
    exact_mod_cast hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact Or.inl h0
  right
  set X : Finset G := Finset.univ.filter (fun g : G => g ^ (k+1) = 1) with hX
  have hXcard : X.card = n + 1 := by
    have hXS : X = insert 1 S := by
      ext g
      simp only [hX, hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases h1 : g = 1
        · left; exact h1
        · right; exact orderOf_eq_prime h h1
      · rintro (rfl | h)
        · simp
        · rw [← h]; exact pow_orderOf_eq_one g
    have h1 : (1:G) ∉ S := by
      simp [hS]
      intro h
      exact absurd h (by omega)
    rw [hXS, Finset.card_insert_of_notMem h1, ← hnS]
  obtain ⟨g0, hg0⟩ : ∃ g : G, orderOf g = k+1 := by
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    simp [hS] at hg
    exact ⟨g, hg⟩
  have hpG : (k+1) ∣ Fintype.card G := hg0 ▸ orderOf_dvd_card
  have hrot : ∀ f : Fin (k+1) → G, (List.ofFn f).prod = 1 →
      (List.ofFn (fun i : Fin (k+1) => f (i+1))).prod = 1 := by
    intro f hf
    have hA : List.ofFn (fun i : Fin (k+1) => f (i+1))
        = (List.ofFn (fun i : Fin k => f i.succ)).concat (f 0) := by
      rw [List.ofFn_succ']
      congr 1
      · congr 1; funext i; congr 1; ext; simp; all_goals omega
      · congr 1; ext; simp
    rw [hA, List.prod_concat]
    rw [List.ofFn_succ, List.prod_cons] at hf
    have h2 : (List.ofFn fun i : Fin k => f i.succ).prod = (f 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hf
    rw [h2, inv_mul_cancel]
  -- the cyclic-index map ℕ → Fin (k+1)
  let nat : ℕ → Fin (k+1) := fun m => ⟨m % (k+1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hsucc : ∀ (m : ℕ) (i : Fin (k+1)), i + nat (m+1) = i + 1 + nat m := by
    intro m i
    apply Fin.ext
    simp only [Fin.val_add, nat, Fin.val_one']
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]
    congr 1
    ring
  have hs' : ∀ m : ℕ, nat (m+1) = nat m + 1 := by
    intro m
    apply Fin.ext
    simp only [Fin.val_add, nat, Fin.val_one']
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]
  have hz : nat 0 = 0 := by apply Fin.ext; simp [nat]
  have hper : ∀ i : Fin (k+1), i + nat (k+1) = i := by
    intro i; apply Fin.ext; simp [nat, Fin.val_add]
  have hval : ∀ i : Fin (k+1), nat i.val = i := by
    intro i; apply Fin.ext
    show i.val % (k+1) = i.val
    exact Nat.mod_eq_of_lt i.isLt
  let Ω := {f : Fin (k+1) → G // (List.ofFn f).prod = 1}
  let T : Function.End Ω := fun f => ⟨fun i => f.1 (i+1), hrot f.1 f.2⟩
  have hTpow : ∀ (m : ℕ) (f : Ω) (i : Fin (k+1)), ((T^m) f).1 i = f.1 (i + nat m) := by
    intro m
    induction m with
    | zero => intro f i; rw [hz, add_zero]; rfl
    | succ m ih =>
      intro f i
      rw [_root_.pow_succ']
      show ((T^m) f).1 (i+1) = _
      rw [ih]
      congr 1
      rw [hsucc]
  have hTfix : T ^ (k+1)^1 = 1 := by
    funext f
    apply Subtype.ext
    funext i
    rw [hTpow, pow_one, hper]
    rfl
  have hconst : ∀ x : Ω, T x = x → ∀ i, x.1 i = x.1 0 := by
    intro x hx
    have hstep : ∀ i, x.1 (i+1) = x.1 i := by
      intro i
      have := congrArg (fun y : Ω => y.1 i) hx
      exact this
    have hm : ∀ m : ℕ, x.1 (nat m) = x.1 0 := by
      intro m
      induction m with
      | zero => rw [hz]
      | succ m ih =>
        rw [hs', hstep, ih]
    intro i
    have := hm i.val
    rwa [hval] at this
  have hcpow : ∀ c : G, (List.ofFn (fun _ : Fin (k+1) => c)).prod = c^(k+1) := by
    intro c; simp [_root_.pow_succ']
  have hconstmem : ∀ x : Ω, T x = x → x.1 0 ^ (k+1) = 1 := by
    intro x hx
    have h := x.2
    have hf : x.1 = fun _ => x.1 0 := funext (hconst x hx)
    rw [hf] at h
    rwa [hcpow] at h
  have hΩcard : Fintype.card Ω = Fintype.card G ^ k := by
    let e : Ω ≃ (Fin k → G) :=
      { toFun := fun f i => f.1 i.castSucc
        invFun := fun g => ⟨Fin.snoc g ((List.ofFn g).prod)⁻¹, by
          rw [List.ofFn_succ']
          simp [List.prod_concat]⟩
        left_inv := by
          intro f
          apply Subtype.ext
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · have h := f.2
            rw [List.ofFn_succ', List.prod_concat] at h
            simp only [Fin.snoc_last]
            exact (eq_inv_of_mul_eq_one_right h).symm
          · simp
        right_inv := by
          intro g
          funext j
          simp }
    rw [Fintype.card_congr e, Fintype.card_fun]
    simp
  have hfixcard : Fintype.card (Function.fixedPoints T) = X.card := by
    let e : Function.fixedPoints T ≃ {g : G // g ∈ X} :=
      { toFun := fun x => ⟨x.1.1 0, by
          rw [hX, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hconstmem _ (Function.mem_fixedPoints.1 x.2)⟩⟩
        invFun := fun g => ⟨⟨fun _ => g.1, by
          rw [hcpow]
          exact (Finset.mem_filter.1 g.2).2⟩, Function.mem_fixedPoints.2 (by
            apply Subtype.ext; funext i; rfl)⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          funext i
          exact (hconst x.1 (Function.mem_fixedPoints.1 x.2) i).symm
        right_inv := by
          intro g
          rfl }
    rw [Fintype.card_congr e, Fintype.card_coe]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := T) (p := k+1) (n := 1) hTfix
  have h0 : Fintype.card Ω ≡ 0 [MOD k+1] :=
    Nat.modEq_zero_iff_dvd.2 (by rw [hΩcard]; exact dvd_pow hpG hk)
  have h3 := hmod.symm.trans h0
  rw [hfixcard, hXcard] at h3
  exact Nat.modEq_zero_iff_dvd.1 h3
