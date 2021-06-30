import homotopy_equivalence
import loop_homotopy

noncomputable theory

class contractible (X : Type _) [topological_space X] :=
(hequiv : homotopy_equivalent X unit)

variables {X : Type _} [topological_space X] [contractible X] {x₀ : X}

instance nonempty_of_contractible : nonempty X :=
begin
  obtain ⟨⟨f, g, h₁, h₂⟩⟩ := @contractible.hequiv X _ _,
  exact ⟨g ()⟩
end

instance path_connected_space_of_contractible : path_connected_space X :=
begin
  refine_struct { nonempty := nonempty_of_contractible },
  obtain ⟨⟨f, g, ⟨h₁⟩, ⟨h₂⟩⟩⟩ := @contractible.hequiv X _ _,
  intros x y,
  refine ⟨path'.to_path _⟩,
  have : ∀ t, f t = (),
  { intro t,
    cases f t, 
    refl },
  let x₀ := g (),
  let p₁ : path' x₀ x,
  { refine_struct { to_fun := { to_fun := λ t, h₁.to_fun (x, t) } },
    continuity,
    simp only [this, homotopy_with.to_fun_zero, continuous_map.comp_coe, continuous_map.coe_mk, 
               function.comp_app],
    simp only [continuous_map.id_apply, homotopy_with.to_fun_one, continuous_map.coe_mk] },
  let p₂ : path' x₀ y,
  { refine_struct { to_fun := { to_fun := λ t, h₁.to_fun (y, t) } },
    continuity,
    simp only [this, homotopy_with.to_fun_zero, continuous_map.comp_coe, continuous_map.coe_mk, 
               function.comp_app],
    simp only [continuous_map.id_apply, homotopy_with.to_fun_one, continuous_map.coe_mk]},
  exact p₁.inv.trans p₂,
  recover,
  exact _inst_2,
end .

example : π₁ () ≃* unit :=
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

-- example : π₁ x₀ ≃* unit :=
-- _
