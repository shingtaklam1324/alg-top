import data.real.pi

open_locale real

lemma cos_pos_iff (t : ℝ) : real.cos t > 0 ↔ 
  t ∈ ⋃ (n : ℤ), set.Ioo (n * (2 * π) - (π / 2) : ℝ) (n * (2 * π) + (π / 2) : ℝ) :=
sorry
-- begin
--   split,
--   { sorry },
--   { rintros ⟨V, ⟨n, rfl⟩, ht⟩,
--      dsimp at ht,
--      have h₁ : real.cos t = real.cos (t - n * (2 * π)),
--      { rw real.cos_sub_int_mul_two_pi },
--      have h₂ : t - n * (2 * π) ∈ set.Ioo (-(π/2)) (π/2),
--      { cases ht, split; linarith },
--      rw h₁,
--      apply real.cos_pos_of_mem_Ioo h₂, }
-- end

-- #check div_div_div_div_eq
-- #check pow_mul
-- -- #check mul_assoc
-- #check list.append_assoc

-- #print notation +
-- #print notation ++
