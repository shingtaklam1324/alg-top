import homotopy_group.basic

/-!
# Simply Connected Spaces

In this file, we define what it means for a path connected space to be simply connected.
-/

variables {X : Type _} [topological_space X] [path_connected_space X]

/--
A path connected space `X` is simply connected if there is a `x₀` such that `π₁ x₀` is trivial.
-/
class simply_connected (X : Type _) [topological_space X] [path_connected_space X] : Prop := 
(hequiv_unit : ∃ x₀ : X, nonempty (π₁ x₀ ≃* unit))

lemma simply_connected_iff_forall : simply_connected X ↔ ∀ x₀ : X, nonempty (π₁ x₀ ≃* unit) :=
begin
  split,
  { rintros ⟨x, ⟨h⟩⟩ y,
    refine ⟨(π₁.mul_equiv_of_path_connected y x).trans h⟩ },
  { intro h,
    constructor,
    use nonempty.some path_connected_space.nonempty,
    apply h }
end
