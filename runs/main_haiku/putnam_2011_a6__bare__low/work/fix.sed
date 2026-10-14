s/    rw \[← hconj ψ, Finset.sum_mul, Finset.mul_sum\]$/    rw [← hconj ψ, Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring/
s/    rw \[mul_comm, Complex.mul_conj'\]/    rw [mul_comm, Complex.mul_conj']; norm_cast/
s/  have e3 : ∀ z : ℂ, z \* starRingEnd ℂ z = /  have e3 : ∀ z : ℂ, starRingEnd ℂ z * z = /
