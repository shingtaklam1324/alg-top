import loop_homotopy
import contractible
import homotopy_isomorphism

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

section contractible

variables [contractible X]

instance simply_connected_of_contractible : simply_connected X :=
begin
  rw simply_connected_iff_forall,
  intros x₀,
  refine ⟨mul_equiv.trans _ π₁.unit⟩,
  let h : homotopy_equivalence X unit := nonempty.some (contractible.hequiv),
  have := @π₁.map_homotopy _ _ x₀ _ _ h,
  convert this,
  cases h.to_fun x₀,
  refl,
end

end contractible
