import homotopy_group.basic

noncomputable theory

def unit.π₁ : π₁ () ≃* unit :=
{ to_fun := λ t, (),
  inv_fun := λ t, 
    ⟦{ to_fun := { to_fun := λ u, () },
       to_fun_zero' := rfl,
       to_fun_one' := rfl }⟧,
  left_inv := begin
    intro a,
    apply quotient.induction_on a,
    intro t,
    rw quotient.eq,
    refine ⟨path_homotopy.of_refl _⟩,
    ext w,
  end,
  right_inv := λ a, begin
    cases a, refl,
  end,
  map_mul' := λ a b, rfl }
