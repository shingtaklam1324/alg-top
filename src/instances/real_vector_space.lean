import contractible
import straight_line_homotopy
import analysis.normed_space.basic

noncomputable theory

instance real_vector_space.contractible {n : ℕ} : contractible (fin n → ℝ) :=
{ hequiv := 
  ⟨{ to_fun := { to_fun := λ p, () },
     inv_fun := { to_fun := λ p, 0 },
     left_inv := ⟨straight_line_homotopy _ _⟩,
     right_inv := 
      ⟨{ to_fun := 
        { to_fun := λ p, () },
         to_fun_zero' := by norm_num,
         to_fun_one' := by norm_num,
         prop := λ t, trivial }⟩ }⟩ }
