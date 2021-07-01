import contractible.basic
import homotopy.straight_line
import analysis.normed_space.basic

noncomputable theory

variables {ι : Type _} [fintype ι]

instance real_vector_space.contractible : contractible (ι → ℝ) :=
{ hequiv := 
  ⟨{ to_fun := { to_fun := λ p, () },
     inv_fun := { to_fun := λ p, 0 },
     left_inv := straight_line_homotopy _ _,
     right_inv := 
      { to_fun := 
        { to_fun := λ p, () },
         to_fun_zero' := by norm_num,
         to_fun_one' := by norm_num,
         prop := λ t, trivial } }⟩ } .
