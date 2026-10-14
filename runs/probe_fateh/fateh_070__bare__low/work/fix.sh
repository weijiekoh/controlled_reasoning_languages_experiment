f=fateh_070.lean
sed -i 's/^    intro a ha$/    suffices key : ∀ a : AdjoinRoot f, 2 * a = 0 → a = 0 from ⟨key, fun a ha => key a (by rwa [mul_comm])⟩\n    intro a ha/' $f
sed -i 's/^    simpa using this$/    exact this/' $f
