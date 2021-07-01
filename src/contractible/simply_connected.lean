import contractible.basic
import simply_connected.basic
import homotopy_group.unit
import homotopy_group.homotopy_isomorphism

section contractible

variables {X : Type _} [topological_space X] [contractible X]

instance simply_connected_of_contractible : simply_connected X :=
begin
  rw simply_connected_iff_forall,
  intros x₀,
  refine ⟨mul_equiv.trans _ unit.π₁⟩,
  let h : homotopy_equiv X unit := nonempty.some (contractible.hequiv),
  have := @π₁.map_homotopy _ _ x₀ _ _ h,
  convert this,
  cases h.to_fun x₀,
  refl,
end

end contractible
