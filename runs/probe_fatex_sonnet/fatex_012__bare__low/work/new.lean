import Mathlib

namespace Problem12

/--
Prove that the ring $\mathbb{Z}[\frac{1+\sqrt{-19}}{2}]$ is a principal ideal domain.
-/
theorem isPrincipalIdealRing_of_quadratic_integer_19 :
  have intpart : ∀ (A B n : ℤ), 0 < n → ¬ (n ∣ A ∧ n ∣ B) → ∃ c d e f : ℤ,
      0 < (c*A - 5*d*B - e*n)^2 + (c*A - 5*d*B - e*n)*(c*B+d*A+d*B - f*n) + 5*(c*B+d*A+d*B - f*n)^2 ∧
      (c*A - 5*d*B - e*n)^2 + (c*A - 5*d*B - e*n)*(c*B+d*A+d*B - f*n) + 5*(c*B+d*A+d*B - f*n)^2 < n^2 := by
    obtain ⟨G, hG⟩ : ∃ G : ℤ → ℤ → ℤ → Prop, ∀ n P Q, G n P Q ↔ ∃ e f : ℤ,
        0 < (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 ∧ (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 < n^2 :=
      ⟨_, fun _ _ _ => Iff.rfl⟩
    have shift : ∀ n P Q k l, G n P Q → G n (P + k*n) (Q + l*n) := by
      intro n P Q k l h
      rw [hG] at h ⊢
      obtain ⟨e, f, h1⟩ := h
      refine ⟨e + k, f + l, ?_⟩
      have e1 : P + k*n - (e+k)*n = P - e*n := by ring
      have e2 : Q + l*n - (f+l)*n = Q - f*n := by ring
      rw [e1, e2]; exact h1
    have neg : ∀ n P Q, G n P Q → G n (-P) (-Q) := by
      intro n P Q h
      rw [hG] at h ⊢
      obtain ⟨e, f, h1, h2⟩ := h
      refine ⟨-e, -f, ?_, ?_⟩
      · have : (-P - -e*n)^2+(-P - -e*n)*(-Q - -f*n)+5*(-Q - -f*n)^2 = (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 := by ring
        rw [this]; exact h1
      · have : (-P - -e*n)^2+(-P - -e*n)*(-Q - -f*n)+5*(-Q - -f*n)^2 = (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 := by ring
        rw [this]; exact h2
    have red : ∀ n S : ℤ, 0 < n → ∃ e : ℤ, -n ≤ S - 2*e*n ∧ S - 2*e*n < n := by
      intro n S hn
      refine ⟨(S+n)/(2*n), ?_⟩
      have h1 := Int.emod_add_mul_ediv (S+n) (2*n)
      have h2 := Int.emod_nonneg (S+n) (show 2*n ≠ 0 by omega)
      have h3 := Int.emod_lt_of_pos (S+n) (show 0 < 2*n by omega)
      generalize (S+n)/(2*n) = e at *
      generalize (S+n)%(2*n) = r at *
      constructor <;> nlinarith
    have L1 : ∀ n P Q f : ℤ, 0 < n → 19*(Q-f*n)^2 < 3*n^2 → ¬ (n ∣ P ∧ n ∣ Q) → G n P Q := by
      intro n P Q f hn hb hnd
      obtain ⟨e, he1, he2⟩ := red n (2*P + (Q - f*n)) hn
      rw [hG]
      refine ⟨e, f, ?_, ?_⟩
      · by_contra h
        push_neg at h
        have hb0 : Q - f*n = 0 := by nlinarith [sq_nonneg (2*(P-e*n)+(Q-f*n)), sq_nonneg (Q-f*n)]
        have ha0 : P - e*n = 0 := by nlinarith
        exact hnd ⟨⟨e, by linarith⟩, ⟨f, by linarith⟩⟩
      · nlinarith [sq_nonneg (2*(P-e*n)+(Q-f*n)), sq_nonneg (Q-f*n)]
    have core : ∀ a b n : ℤ, 0 < n → 0 < b → 2*b ≤ n → -n ≤ 2*a+b → 2*a+b ≤ n → 
        ∃ c d : ℤ, G n (c*a - 5*d*b) (c*b+d*a+d*b) := by
      intro a b n hn hb hb2 ha1 ha2
      by_cases hs : 19*b^2 < 3*n^2
      · refine ⟨1, 0, ?_⟩
        rw [hG]
        refine ⟨0, 0, ?_, ?_⟩
        · nlinarith [sq_nonneg (2*a+b), sq_nonneg b]
        · nlinarith [sq_nonneg (2*a+b), sq_nonneg b]
      · push_neg at hs
        by_cases hd : n ∣ 2*a ∧ n ∣ 2*b
        · obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := hd
          have hk1 : k = 1 := by
            have : 0 < k := by by_contra h; push_neg at h; nlinarith
            have : k ≤ 1 := by by_contra h; push_neg at h; nlinarith
            omega
          subst hk1
          have hj1 : -1 ≤ j := by by_contra h; push_neg at h; nlinarith
          have hj2 : j ≤ 0 := by by_contra h; push_neg at h; nlinarith
          have : j = 0 ∨ j = -1 := by omega
          rcases this with rfl | rfl
          · refine ⟨1, 1, ?_⟩
            rw [hG]
            refine ⟨-2, 1, ?_, ?_⟩ <;> nlinarith
          · refine ⟨0, 1, ?_⟩
            rw [hG]
            refine ⟨-2, 0, ?_, ?_⟩ <;> nlinarith
        · refine ⟨2, 0, ?_⟩
          have := L1 n (2*a) (2*b) 1 hn ?_ hd
          · simpa using this
          · nlinarith
    intro A B n hn h
    obtain ⟨f, hf1, hf2⟩ := red n (2*B) hn
    obtain ⟨b, hb⟩ : ∃ b, b = B - f*n := ⟨_, rfl⟩
    obtain ⟨e, he1, he2⟩ := red n (2*A+b) hn
    obtain ⟨a, ha⟩ : ∃ a, a = A - e*n := ⟨_, rfl⟩
    have hA : A = a + e*n := by linarith
    have hB : B = b + f*n := by linarith
    subst hA hB
    have hab : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨⟨e, by ring⟩, ⟨f, by ring⟩⟩
    have key : ∃ c d : ℤ, G n (c*a - 5*d*b) (c*b+d*a+d*b) := by
      rcases lt_trichotomy b 0 with hneg | hzero | hpos
      · obtain ⟨c, d, hcd⟩ := core (-a) (-b) n hn (by linarith) (by linarith) (by linarith) (by linarith)
        refine ⟨c, d, ?_⟩
        have := neg _ _ _ hcd
        convert this using 2 <;> ring
      · subst hzero
        have ha0 : a ≠ 0 := fun h0 => hab ⟨h0, rfl⟩
        refine ⟨1, 0, ?_⟩
        rw [hG]
        refine ⟨0, 0, ?_, ?_⟩
        · have := sq_pos_of_ne_zero ha0
          nlinarith
        · nlinarith
      · exact core a b n hn hpos (by linarith) (by linarith) (by linarith)
    obtain ⟨c, d, hcd⟩ := key
    have := shift n _ _ (c*e - 5*d*f) (c*f + d*e + d*f) hcd
    rw [hG] at this
    obtain ⟨e', f', h1, h2⟩ := this
    refine ⟨c, d, e', f', ?_, ?_⟩
    · convert h1 using 3 <;> ring
    · convert h2 using 3 <;> ring
  obtain ⟨α, hαdef⟩ : ∃ α : ℂ, α = (1 + (Real.sqrt 19) * Complex.I) / 2 := ⟨_, rfl⟩
  rw [← hαdef]
  have hs : ((Real.sqrt 19 : ℝ):ℂ)^2 = 19 := by
    rw [← Complex.ofReal_pow]; simp [Real.sq_sqrt]
  have hα2 : α*α = α - 5 := by
    rw [hαdef]
    linear_combination (Complex.I^2/4)*hs + (19/4)*Complex.I_sq
  have nsq : ∀ a b : ℤ, Complex.normSq ((a:ℂ) + b*α) = (a^2+a*b+5*b^2 : ℤ) := by
    intro a b
    have : (a:ℂ) + b*α = ⟨a + b/2, b*Real.sqrt 19/2⟩ := by
      apply Complex.ext <;> simp [hαdef] <;> ring
    rw [this, Complex.normSq_mk]
    have h19 : Real.sqrt 19 * Real.sqrt 19 = 19 := Real.mul_self_sqrt (by norm_num)
    push_cast
    nlinarith [h19]
  have mem : ∀ z : ℂ, z ∈ Algebra.adjoin ℤ {α} ↔ ∃ a b : ℤ, z = a + b*α := by
    intro z
    constructor
    · intro hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        exact ⟨0, 1, by simp [hx]⟩
      | algebraMap r => exact ⟨r, 0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, b, rfl⟩ := hx
        obtain ⟨c, d, rfl⟩ := hy
        exact ⟨a+c, b+d, by push_cast; ring⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, b, rfl⟩ := hx
        obtain ⟨c, d, rfl⟩ := hy
        refine ⟨a*c - 5*b*d, a*d+b*c+b*d, ?_⟩
        push_cast
        linear_combination (b*d : ℂ)*hα2
    · rintro ⟨a, b, rfl⟩
      have h1 : α ∈ Algebra.adjoin ℤ {α} := Algebra.subset_adjoin rfl
      exact add_mem (intCast_mem _ a) (mul_mem (intCast_mem _ b) h1)
  refine ⟨?_, inferInstance⟩
  have hnat : ∀ z : Algebra.adjoin ℤ {α}, ∃ m : ℕ, Complex.normSq (z:ℂ) = m := by
    intro z
    obtain ⟨a, b, hz⟩ := (mem z).1 z.2
    rw [hz, nsq]
    have h0 : (0:ℝ) ≤ ((a^2+a*b+5*b^2 : ℤ):ℝ) := by
      have := Complex.normSq_nonneg (z:ℂ); rwa [hz, nsq] at this
    have h0' : 0 ≤ a^2+a*b+5*b^2 := by exact_mod_cast h0
    refine ⟨(a^2+a*b+5*b^2).toNat, ?_⟩
    have := Int.toNat_of_nonneg h0'
    exact_mod_cast this.symm
  have DH : ∀ x y : Algebra.adjoin ℤ {α}, y ≠ 0 → y ∣ x ∨ ∃ s t : Algebra.adjoin ℤ {α},
      0 < Complex.normSq ((s*x - t*y : Algebra.adjoin ℤ {α}) : ℂ) ∧
      Complex.normSq ((s*x - t*y : Algebra.adjoin ℤ {α}) : ℂ) < Complex.normSq (y:ℂ) := by
    intro x y hy
    obtain ⟨a, b, hx⟩ := (mem x).1 x.2
    obtain ⟨c, d, hy'⟩ := (mem y).1 y.2
    have hynz : Complex.normSq (y:ℂ) ≠ 0 := by
      rw [Ne, Complex.normSq_eq_zero]
      intro h; apply hy; exact Subtype.ext h
    have hny : Complex.normSq (y:ℂ) = ((c^2+c*d+5*d^2 : ℤ):ℝ) := by rw [hy', nsq]
    have hnpos : 0 < c^2+c*d+5*d^2 := by
      have : (0:ℝ) < ((c^2+c*d+5*d^2 : ℤ):ℝ) := by
        rw [← hny]; exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hynz)
      exact_mod_cast this
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n = c^2+c*d+5*d^2 := ⟨_, rfl⟩
    rw [← hn] at hnpos hny
    set yb : ℂ := ((c+d : ℤ):ℂ) - d*α with hyb
    have hybm : yb ∈ Algebra.adjoin ℤ {α} := (mem _).2 ⟨c+d, -d, by rw [hyb]; push_cast; ring⟩
    have hyy : (y:ℂ) * yb = n := by
      rw [hy', hyb, hn]; push_cast
      linear_combination (-(d:ℂ)^2)*hα2
    have hnyb : Complex.normSq yb = n := by
      have := nsq (c+d) (-d)
      rw [hyb, hn]
      have e : ((c+d:ℤ):ℂ) - d*α = ((c+d:ℤ):ℂ) + ((-d:ℤ):ℂ)*α := by push_cast; ring
      rw [e, this]; push_cast; ring
    have hxm : (x:ℂ) * yb ∈ Algebra.adjoin ℤ {α} := mul_mem x.2 hybm
    obtain ⟨A, B, hAB⟩ := (mem _).1 hxm
    by_cases hdiv : n ∣ A ∧ n ∣ B
    · left
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hdiv
      have hrm : ((p:ℂ) + q*α) ∈ Algebra.adjoin ℤ {α} := (mem _).2 ⟨p, q, rfl⟩
      refine ⟨⟨_, hrm⟩, ?_⟩
      apply Subtype.ext
      have hybne : yb ≠ 0 := by
        intro h0; rw [h0] at hnyb; simp at hnyb
        have : (0:ℝ) < n := by exact_mod_cast hnpos
        linarith
      apply mul_right_cancel₀ hybne
      show (x:ℂ) * yb = (y:ℂ) * ((p:ℂ) + q*α) * yb
      rw [hAB, hp, hq]
      have : (y:ℂ) * ((p:ℂ) + q*α) * yb = ((y:ℂ)*yb) * ((p:ℂ) + q*α) := by ring
      rw [this, hyy]; push_cast; ring
    · right
      obtain ⟨c', d', e, f, h1, h2⟩ := intpart A B n hnpos hdiv
      have hsm : ((c':ℂ) + d'*α) ∈ Algebra.adjoin ℤ {α} := (mem _).2 ⟨c', d', rfl⟩
      have htm : ((e:ℂ) + f*α) ∈ Algebra.adjoin ℤ {α} := (mem _).2 ⟨e, f, rfl⟩
      refine ⟨⟨_, hsm⟩, ⟨_, htm⟩, ?_⟩
      have hu : (((c':ℂ)+d'*α)*(x:ℂ) - ((e:ℂ)+f*α)*(y:ℂ)) * yb
          = (((c'*A - 5*d'*B - e*n : ℤ):ℂ) + ((c'*B+d'*A+d'*B - f*n : ℤ):ℂ) * α) := by
        push_cast
        linear_combination ((c':ℂ)+d'*α)*hAB - ((e:ℂ)+f*α)*hyy + (d'*B:ℂ)*hα2
      have hN := congrArg Complex.normSq hu
      rw [map_mul, nsq, hnyb] at hN
      have hu2 : ((⟨_, hsm⟩ * x - ⟨_, htm⟩ * y : Algebra.adjoin ℤ {α}) : ℂ) = ((c':ℂ)+d'*α)*(x:ℂ) - ((e:ℂ)+f*α)*(y:ℂ) := rfl
      rw [hu2]
      rw [hny]
      have hnr : (0:ℝ) < n := by exact_mod_cast hnpos
      have h1' : (0:ℝ) < ((c'*A - 5*d'*B - e*n : ℤ):ℝ)^2 + ((c'*A - 5*d'*B - e*n : ℤ):ℝ)*((c'*B+d'*A+d'*B - f*n : ℤ):ℝ) + 5*((c'*B+d'*A+d'*B - f*n : ℤ):ℝ)^2 := by exact_mod_cast h1
      have h2' : ((c'*A - 5*d'*B - e*n : ℤ):ℝ)^2 + ((c'*A - 5*d'*B - e*n : ℤ):ℝ)*((c'*B+d'*A+d'*B - f*n : ℤ):ℝ) + 5*((c'*B+d'*A+d'*B - f*n : ℤ):ℝ)^2 < (n:ℝ)^2 := by exact_mod_cast h2
      push_cast at hN h1' h2'
      constructor
      · by_contra hc
        push_neg at hc
        nlinarith [Complex.normSq_nonneg (((c':ℂ)+d'*α)*(x:ℂ) - ((e:ℂ)+f*α)*(y:ℂ))]
      · by_contra hc
        push_neg at hc
        nlinarith
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · exact ⟨⟨0, by rw [hI]; simp⟩⟩
  obtain ⟨z0, hz0, hz0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ z : Algebra.adjoin ℤ {α}, z ∈ I ∧ z ≠ 0 ∧ Complex.normSq (z:ℂ) = n := by
    obtain ⟨m, hm⟩ := hnat z0
    exact ⟨m, z0, hz0, hz0ne, hm⟩
  classical
  obtain ⟨y, hyI, hy0, hyn⟩ := Nat.find_spec hex
  refine ⟨⟨y, ?_⟩⟩
  ext x
  show x ∈ I ↔ x ∈ Ideal.span {y}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    by_contra hnd
    rcases DH x y hy0 with h | ⟨s, t, h1, h2⟩
    · exact hnd h
    · have hw : s*x - t*y ∈ I := I.sub_mem (I.mul_mem_left s hx) (I.mul_mem_left t hyI)
      have hw0 : s*x - t*y ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
      obtain ⟨m, hm⟩ := hnat (s*x - t*y)
      have hlt : m < Nat.find hex := by
        have : (m:ℝ) < (Nat.find hex : ℝ) := by rw [← hm, ← hyn]; exact h2
        exact_mod_cast this
      exact Nat.find_min hex hlt ⟨_, hw, hw0, hm⟩
  · rintro ⟨r, rfl⟩; exact I.mul_mem_right r hyI

end Problem12
