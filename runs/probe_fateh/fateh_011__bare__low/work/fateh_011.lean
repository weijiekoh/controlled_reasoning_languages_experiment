import Mathlib

/--
Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.
-/
theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  have hp : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime (Nat.card H)) := by rw [hH]; exact hp
  haveI : IsCyclic H := isCyclic_of_prime_card hH
  have hA : Nat.card (MulAut H) = 16 := by
    rw [IsCyclic.card_mulAut, hH]; decide
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : orderOf (MulAut.conjNormal (H := H) g) ∣ 16 := hA ▸ orderOf_dvd_natCard _
  have h2 : orderOf (MulAut.conjNormal (H := H) g) ∣ 3825 :=
    (orderOf_map_dvd _ g).trans (h ▸ orderOf_dvd_natCard g)
  have h3 : orderOf (MulAut.conjNormal (H := H) g) = 1 := by
    have := Nat.dvd_gcd h1 h2
    simpa using this
  have h4 := orderOf_eq_one_iff.mp h3
  have h5 := congrArg (fun f : MulAut H => (f ⟨x, hx⟩ : H).1) h4
  simp [MulAut.conjNormal_apply] at h5
  have h6 := congrArg (· * g) h5
  simp at h6
  exact h6
