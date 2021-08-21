import instances.real_vector_space

/-!
# Instances `ℝ`

In this file, we prove that for a `fintype` `ι`, `ι → ℝ` is contractible.
-/

noncomputable theory

def real_homeo_fin1 : homeomorph (fin 1 → ℝ) ℝ :=
{ to_fun := λ f, f 0,
  inv_fun := λ t _, t,
  left_inv := λ t, by { ext, fin_cases x },
  right_inv := λ t, by simp,
  continuous_to_fun := by continuity,
  continuous_inv_fun := by continuity }

instance real.contractible : contractible ℝ :=
⟨⟨(homotopy_equiv.of_homeomorph real_homeo_fin1).symm.trans real_vector_space.contractible.1.some⟩⟩
