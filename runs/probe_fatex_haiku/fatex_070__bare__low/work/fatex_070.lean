import Mathlib

namespace Problem70

/--
All rings considered are noetherian.
Show that if \( R \) is an integral domain contained in the local ring \( (S, Q) \),
then there is a minimal prime of \( S \) contracting to \( 0 \) in \( R \).
-/
theorem exists_minimalPrime_map_zero (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [NoZeroSMulDivisors R S] :
    ∃ (p : minimalPrimes S), Ideal.comap (algebraMap R S) p.1 = ⊥ := by
  classical
  let M : Submonoid R :=
    { carrier := {r | r ≠ 0}
      mul_mem' := fun {a b} ha hb => mul_ne_zero ha hb
      one_mem' := one_ne_zero }
  let T : Submonoid S := Submonoid.map (algebraMap R S) M
  have hnz : (1 : S) ≠ 0 := one_ne_zero
  have hker : ∀ r : R, algebraMap R S r = 0 → r = 0 := by
    intro r h
    have h2 : r • (1 : S) = 0 := by rw [Algebra.smul_def, h, zero_mul]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hnz
  have hdisj : Disjoint ((⊥ : Ideal S) : Set S) (T : Set S) := by
    rw [Set.disjoint_left]
    intro x hx hxT
    rw [SetLike.mem_coe, Ideal.mem_bot] at hx
    obtain ⟨r, hr, hrx⟩ := hxT
    rw [hx] at hrx
    exact hr (hker r hrx)
  obtain ⟨Q, hQp, _, hQdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal S) T hdisj
  obtain ⟨p, hpmin, hpQ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := Q) bot_le
  refine ⟨⟨p, hpmin⟩, ?_⟩
  apply eq_bot_iff.mpr
  intro r hr
  rw [Ideal.mem_bot]
  by_contra hr0
  have hrp : algebraMap R S r ∈ p := hr
  have hrQ : algebraMap R S r ∈ Q := hpQ hrp
  have hrT : algebraMap R S r ∈ (T : Set S) := Submonoid.mem_map.mpr ⟨r, hr0, rfl⟩
  exact Set.disjoint_left.mp hQdisj hrQ hrT

end Problem70
