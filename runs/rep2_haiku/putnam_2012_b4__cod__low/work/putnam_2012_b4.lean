import Mathlib

open Matrix Function Real Topology Filter

noncomputable abbrev putnam_2012_b4_solution : Prop := True
set_option maxHeartbeats 4000000 in
/--
Suppose that $a_0 = 1$ and that $a_{n+1} = a_n + e^{-a_n}$ for $n=0,1,2,\dots$. Does $a_n - \log n$
have a finite limit as $n \to \infty$? (Here $\log n = \log_e n = \ln n$.)
-/
theorem putnam_2012_b4
(a : ℕ → ℝ)
(ha0 : a 0 = 1)
(han : ∀ n : ℕ, a (n + 1) = a n + exp (-a n))
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) := by
  have he := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  -- F1 : lower bound
  have F1 : ∀ n : ℕ, (n:ℝ) + exp 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      have hpos : (0:ℝ) < exp (a n) := exp_pos _
      have hx : exp (a (n+1)) = exp (a n) * exp ((exp (a n))⁻¹) := by
        rw [han n, exp_add, Real.exp_neg]
      have h1 := Real.add_one_le_exp ((exp (a n))⁻¹)
      have hB : exp (a n) * ((exp (a n))⁻¹ + 1) = exp (a n) + 1 := by
        field_simp
        ring
      have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
      rw [hx]
      push_cast
      linarith
  -- log bounds
  have hlogb : ∀ m : ℝ, 1 ≤ m → (m+1)⁻¹ ≤ log (m+1) - log m ∧ log (m+1) - log m ≤ m⁻¹ := by
    intro m hm
    have hm0 : 0 < m := by linarith
    have e2 : log ((m+1)/m) = log (m+1) - log m := Real.log_div (by positivity) (by positivity)
    constructor
    · have h := Real.one_sub_inv_le_log_of_pos (x := (m+1)/m) (by positivity)
      rw [inv_div, e2] at h
      have h3 : 1 - m/(m+1) = (m+1)⁻¹ := by field_simp; ring
      linarith
    · have h := Real.log_le_sub_one_of_pos (x := (m+1)/m) (by positivity)
      rw [e2] at h
      have h3 : (m+1)/m - 1 = m⁻¹ := by field_simp; ring
      linarith
  have hlogstep : ∀ m : ℝ, 1 ≤ m → m⁻¹ ≤ 2 * (log (m+1) - log m) := by
    intro m hm
    have h := (hlogb m hm).1
    have hm0 : 0 < m := by linarith
    have h4 : m⁻¹ ≤ 2 * (m+1)⁻¹ := by
      have e1 : m⁻¹ = 1/m := (one_div m).symm
      have e3 : 2 * (m+1)⁻¹ = 2/(m+1) := by ring
      rw [e1, e3, div_le_div_iff₀ hm0 (by positivity)]
      nlinarith
    linarith
  -- sqrt-type log bound
  have hlogsqrt : ∀ x : ℝ, 1 ≤ x → log (x+1) ≤ 4 * √x := by
    intro x hx
    have h := Real.log_le_rpow_div (x := x+1) (ε := 1/2) (by linarith) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    have hs : √(x+1) ≤ 2 * √x := by
      have h1 := Real.sq_sqrt (show (0:ℝ) ≤ x+1 by linarith)
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ x by linarith)
      have h3 := Real.sqrt_nonneg x
      have h4 := Real.sqrt_nonneg (x+1)
      nlinarith
    have : √(x+1) / (1/2) = 2 * √(x+1) := by ring
    linarith
  have ha_nonneg : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    have h := F1 n
    have h0 : exp 0 ≤ exp (a n) := by
      rw [exp_zero]
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact Real.exp_le_exp.mp h0
  -- F2 : upper bound
  have F2 : ∀ n : ℕ, exp (a n) ≤ n + exp 1 + 2 * log (n+1) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      have hB1 := F1 n
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have hBpos : (0:ℝ) < exp (a n) := exp_pos _
      have hBge1 : (1:ℝ) ≤ exp (a n) := by linarith
      have hy0 : 0 ≤ (exp (a n))⁻¹ := inv_nonneg.2 hBpos.le
      have hy1 : (exp (a n))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBge1
      have habs := Real.abs_exp_sub_one_sub_id_le (x := (exp (a n))⁻¹)
        (by rw [abs_of_nonneg hy0]; exact hy1)
      have hexpy : exp ((exp (a n))⁻¹) ≤ 1 + (exp (a n))⁻¹ + ((exp (a n))⁻¹)^2 := by
        have := (abs_le.mp habs).2
        linarith
      have hBn : exp (a (n+1)) = exp (a n) * exp ((exp (a n))⁻¹) := by
        rw [han n, exp_add, Real.exp_neg]
      have hBy : exp (a n) * (exp (a n))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hBpos)
      have hid : exp (a n) * (1 + (exp (a n))⁻¹ + ((exp (a n))⁻¹)^2)
          = exp (a n) + 1 + (exp (a n))⁻¹ := by
        linear_combination (1 + (exp (a n))⁻¹) * hBy
      have h5 := mul_le_mul_of_nonneg_left hexpy hBpos.le
      have hyle : (exp (a n))⁻¹ ≤ ((n:ℝ)+1)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
      have hls := hlogstep ((n:ℝ)+1) (by linarith)
      rw [hBn]
      push_cast
      nlinarith
  -- key estimate
  have key : ∀ n : ℕ, 1 ≤ n →
      |(a (n+1) - log ((n+1:ℕ):ℝ)) - (a n - log (n:ℝ))| ≤ 13 / (√(n:ℝ) * n) := by
    intro n hn
    have hx1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hx0 : (0:ℝ) < n := by linarith
    set x : ℝ := (n:ℝ) with hxdef
    have hs1 : (1:ℝ) ≤ √x := by
      rw [show (1:ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt hx1
    have hsq : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hlog := hlogsqrt x hx1
    have hB1 := F1 n
    have hB2 := F2 n
    have hc : (a (n+1) - log ((n+1:ℕ):ℝ)) - (a n - log (n:ℝ))
        = (exp (a n))⁻¹ - (log (x+1) - log x) := by
      rw [han n, Real.exp_neg]
      push_cast
      ring
    rw [hc]
    have hl := hlogb x hx1
    set B := exp (a n) with hBdef
    have hBpos : 0 < B := exp_pos _
    set L := log (x+1) - log x with hLdef
    set E := exp 1 + 2 * log (x+1) with hEdef
    have hB1' : x + exp 1 ≤ B := hB1
    have hB2' : B ≤ x + E := by rw [hEdef]; linarith
    have hE : 1 + E ≤ 13 * √x := by
      have : exp 1 ≤ 3 := by linarith
      linarith
    have hinvB1 : (x + E)⁻¹ ≤ B⁻¹ := inv_anti₀ hBpos hB2'
    have hinvB2 : B⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 (by linarith)
    have hEnn : 0 ≤ E := by
      have : 0 ≤ log (x+1) := Real.log_nonneg (by linarith)
      have : 0 ≤ exp 1 := (exp_pos 1).le
      linarith
    have hpos13 : 0 < √x * x := by positivity
    have hfin_up : B⁻¹ - L ≤ 13 / (√x * x) := by
      have h1 : B⁻¹ - L ≤ x⁻¹ - (x+1)⁻¹ := by linarith [hl.1]
      have h2 : x⁻¹ - (x+1)⁻¹ ≤ 13 / (√x * x) := by
        have e4 : x⁻¹ - (x+1)⁻¹ = 1 / (x * (x+1)) := by field_simp; ring
        have h6 : √x ≤ x + 1 := by nlinarith
        have h7 : 1 / (x * (x+1)) ≤ 1 / (√x * x) := by
          apply one_div_le_one_div_of_le hpos13
          nlinarith
        have h8 : 1 / (√x * x) ≤ 13 / (√x * x) := by
          apply div_le_div_of_nonneg_right _ hpos13.le
          norm_num
        rw [e4]
        linarith
      linarith
    have hfin_lo : -(13 / (√x * x)) ≤ B⁻¹ - L := by
      have h1 : (x+E)⁻¹ - x⁻¹ ≤ B⁻¹ - L := by linarith [hl.2]
      have e5 : (x+E)⁻¹ - x⁻¹ = -(E / (x * (x+E))) := by
        field_simp
        ring
      have h2 : E / (x * (x+E)) ≤ 13 / (√x * x) := by
        have h3 : E / (x * (x+E)) ≤ E / (x * x) := by
          apply div_le_div_of_nonneg_left hEnn (by positivity)
          nlinarith
        have h4 : E / (x * x) ≤ 13 / (√x * x) := by
          rw [div_le_div_iff₀ (by positivity) hpos13]
          have hh : E * (√x * x) ≤ 13 * √x * (√x * x) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          nlinarith [hsq]
        linarith
      linarith
    exact abs_le.mpr ⟨hfin_lo, hfin_up⟩
  set c : ℕ → ℝ := fun n => a n - log (n:ℝ) with hcdef
  have hsum0 : Summable (fun n : ℕ => 13 / (√(n:ℝ) * n)) := by
    have hfun : (fun n : ℕ => 13 / (√(n:ℝ) * n)) = fun n : ℕ => 13 * (1 / (n:ℝ)^((3:ℝ)/2)) := by
      funext n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hx : (0:ℝ) < n := by exact_mod_cast h
        have h32 : (n:ℝ)^((3:ℝ)/2) = √(n:ℝ) * n := by
          rw [Real.sqrt_eq_rpow, show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
        rw [h32]
        ring
    rw [hfun]
    exact (Real.summable_one_div_nat_rpow.2 (by norm_num : (1:ℝ) < 3/2)).mul_left 13
  have hS : Summable (fun n : ℕ => 13 / (√((n+1:ℕ):ℝ) * ((n+1:ℕ):ℝ))) :=
    (summable_nat_add_iff 1).mpr hsum0
  have hgS : Summable (fun n : ℕ => c (n+1+1) - c (n+1)) := by
    apply summable_abs_iff.mp
    apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => key (n+1) (by omega)) hS
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (c (i+1+1) - c (i+1)) = c (n+1) - c 1 := by
    intro n
    have := Finset.sum_range_sub (fun i => c (i+1)) n
    simpa using this
  have hT := hgS.hasSum.tendsto_sum_nat
  have h2 := hT.add_const (c 1)
  simp only [htel, sub_add_cancel] at h2
  have hc : Tendsto c atTop (𝓝 (∑' n : ℕ, (c (n+1+1) - c (n+1)) + c 1)) :=
    (tendsto_add_atTop_iff_nat 1).mp h2
  show (∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ True
  exact ⟨fun _ => trivial, fun _ => ⟨_, hc⟩⟩
