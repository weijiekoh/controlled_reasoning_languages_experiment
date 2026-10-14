/have := one_add_mul_self_le_rpow_one_add/{
N
c\
    have hx : (0:ℝ) < 1 / b n := by have := bpos n; positivity\
    have := one_add_mul_self_le_rpow_one_add (s := 1/b n) (by linarith) hp1
}
s/^        field_simp$/        have := (hpos n).ne'; have := (Real.rpow_pos_of_pos (hpos n) ((1:ℝ)\/k)).ne'; field_simp/
