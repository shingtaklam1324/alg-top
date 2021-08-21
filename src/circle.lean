import analysis.complex.circle
import data.real.pi

noncomputable theory

def X_pos : set circle := { z | complex.re z > 0 }
def X_neg : set circle := { z | complex.re z < 0 }
def Y_pos : set circle := { z | complex.im z > 0 }
def Y_neg : set circle := { z | complex.im z < 0 }

open complex
open_locale real

lemma cos_pos_iff (t : ℝ) : real.cos t > 0 ↔ t ∈ ⋃ (n : ℤ), set.Ioo ((n-1/4) * 2 * π : ℝ) ((n + 1/4) * 2 * π) :=
begin
  refine ⟨λ ht, _, _⟩,
  { by_contra,
     }
end

-- example : exp_map_circle ⁻¹' X_pos = ⋃ (n : ℤ), set.Ioo ((n-1/4) * 2 * π) ((n + 1/4) * 2 * π) :=
-- begin
--   ext1 t, refine ⟨_, _⟩,
--   { rintro ht,
--     rw set.mem_preimage at ht,
--     sorry },
--   { rintro ⟨u, ⟨n, rfl⟩, htu⟩,
--     rw set.mem_preimage,
--     change complex.re (complex.exp _) > 0,
--     rw exp_re,
--     simp,
--     sorry
--     -- rw mul_I_im
--     -- squeeze_simp,
--      }
-- end

/-
Prop : Each point z ∈ S^1 has a nbhd U whith the following property:

ε⁻¹(U) is a countable union of disjoint open intervals (U_n) such that ε restricts to a 
homeomorphism from U_n onto U
-/
