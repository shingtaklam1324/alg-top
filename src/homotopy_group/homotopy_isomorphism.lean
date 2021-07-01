import homotopy_group.basic
import homotopy.equiv

/-!
# Homotopy equivalences induce group isomorphisms

In this file, we show that given `h : homotopy_equiv X Y`, then we have a group isomorphism
`π₁ x₀ ≃* π₁ (h x₀)`.
-/

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y] {x₀ : X} {f g : C(X, Y)}

/--
Given a homotopy between `f` and `g`, we have a path between `f x₀` and `g x₀` given by the 
homotopy.
-/
def homotopy.path (h : homotopy f g) : path' (f x₀) (g x₀) :=
{ to_fun := 
  { to_fun := λ r, h (x₀, r) },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num } .

lemma mul_equiv.symm_to_monoid_hom_comp_to_monoid_hom {M N : Type _} [monoid M] [monoid N] 
  (h : M ≃* N) : h.symm.to_monoid_hom.comp h.to_monoid_hom = monoid_hom.id _ :=
begin
  ext,
  unfold mul_equiv.symm equiv.symm,
  simp,
end

namespace π₁

private def F (l : loop x₀) (h : homotopy f g) : C(ℝ × ℝ, Y) :=
{ to_fun := λ p, h (l p.1, p.2) }

private def l₁ : path' ((0, 1) : ℝ × ℝ) (1, 1) :=
{ to_fun := { to_fun := λ s, (s, 1) },
  to_fun_zero' := by simp,
  to_fun_one' := by simp } .

private def l₂₁ : path' ((0, 1) : ℝ × ℝ) (0, 0) :=
{ to_fun := { to_fun := λ s, (0, 1 - s) },
  to_fun_zero' := by simp,
  to_fun_one' := by simp } .

private def l₂₂ : path' ((0, 0) : ℝ × ℝ) (1, 0) :=
{ to_fun := { to_fun := λ s, (s, 0) },
  to_fun_zero' := by simp,
  to_fun_one' := by simp } .

private def l₂₃ : path' ((1, 0) : ℝ × ℝ) (1, 1) :=
{ to_fun := { to_fun := λ s, (1, s) },
  to_fun_zero' := by simp,
  to_fun_one' := by simp } .

private def l₂ := (l₂₁.trans l₂₂).trans l₂₃

private def homotopy_l₁_l₂ : path_homotopy l₁ l₂ :=
{ to_fun := { to_fun := λ p, (1 - p.2) • l₁ p.1 + p.2 • l₂ p.1 },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num,
  prop := λ t, by norm_num } .

private def l₁_map (l : loop x₀) (h : homotopy f g) : (l₁.map (F l h) : ℝ → Y) = (l.map g) :=
begin
  ext t,
  simp only [F, l₁, path'.map, path'.coe_apply, homotopy_with.to_fun_one, path'.mk_apply, 
             continuous_map.comp_coe, continuous_map.coe_mk, function.comp_app],
end

private def l₂_map (l : loop x₀) (h : homotopy f g) : 
  (l₂.map (F l h) : ℝ → Y) = ((h.path.inv.trans (l.map f)).trans h.path) :=
begin
  ext t,
  simp only [path'.coe_apply, path'.mk_apply, continuous_map.comp_coe, F, continuous_map.coe_mk, 
             l₂, path'.map, function.comp_app, path'.trans],
  split_ifs with h₁ h₂,
  { simp [homotopy.path, l₂₁, path'.inv] },
  { simp [homotopy.path, l₂₂, path'.inv] },
  { simp [homotopy.path, l₂₃, path'.inv] },
end .

private def change_of_basepoint_comp_map_eq_map_aux (l : loop x₀) (h : homotopy f g) :=
  path_homotopy.change_end_points (homotopy_l₁_l₂.map _) (l₁_map l h) (l₂_map l h)

private lemma change_of_basepoint_comp_map_eq_map (h : homotopy f g) : 
  (π₁.change_of_basepoint h.path : π₁ (f x₀) ≃* π₁ (g x₀)).to_monoid_hom.comp (π₁.map f) 
    = π₁.map g :=
begin
  ext x,
  apply quotient.induction_on x,
  intro l,
  simp only [π₁.change_of_basepoint, π₁.map, mul_equiv.coe_to_monoid_hom, quotient.lift_mk, 
    mul_equiv.coe_mk, function.comp_app, monoid_hom.coe_mk, monoid_hom.coe_comp, quotient.eq],
  exact ⟨(change_of_basepoint_comp_map_eq_map_aux l h).symm⟩,
end .

private lemma bij_helper₁ {x₀ : X} (h : homotopy_equiv X Y) : 
  (π₁.map (h.symm : C(Y, X))).comp (π₁.map (h : C(X, Y)) : π₁ x₀ →* _) = 
    (@π₁.change_of_basepoint _ _ x₀ _ (homotopy.path h.left_inv.some.symm)).to_monoid_hom :=
calc (π₁.map h.inv_fun).comp (π₁.map h.to_fun : π₁ x₀ →* _) = 
  (@π₁.change_of_basepoint _ _ x₀ _ (homotopy.path h.left_inv.some.symm)).to_monoid_hom.comp 
    (π₁.map continuous_map.id) : by rw [change_of_basepoint_comp_map_eq_map, π₁.map_comp]
                       ... = _ : by { ext, simp [continuous_map.id_apply] } .

private def u (h : homotopy_equiv X Y) : path' (h x₀) (h (h.symm (h x₀))) :=
  homotopy.path (h.right_inv.some.symm)

private lemma bij_helper₂ {x₀ : X} (h : homotopy_equiv X Y) :
  (@π₁.change_of_basepoint _ _ (h x₀) _ (u h)).to_monoid_hom = 
    (π₁.map (h : C(X, Y))).comp (π₁.map (h.symm : C(Y, X)) : π₁ _ →* _) :=
calc (@π₁.change_of_basepoint _ _ (h.to_fun x₀) _ (u h)).to_monoid_hom =
  (@π₁.change_of_basepoint _ _ (h.to_fun x₀) _ (u h)).to_monoid_hom.comp 
    (π₁.map continuous_map.id) : by { ext, simp [continuous_map.id_apply], }
  ... = (π₁.map h.to_fun).comp (π₁.map h.inv_fun : π₁ _ →* _) : 
    by { rw [u, change_of_basepoint_comp_map_eq_map, π₁.map_comp] } .

/--
Given `h : homotopy_equiv X Y`, we have an induced group isomorphism.
-/
def map_homotopy {Y : Type _} [topological_space Y] (h : homotopy_equiv X Y) : 
  π₁ x₀ ≃* π₁ (h.to_fun x₀) :=
  mul_equiv.of_bijective (π₁.map h.to_fun)
begin
  have hyp : function.bijective (π₁.map h.inv_fun : π₁ (h.to_fun x₀) →* _),
  { split,
    { have : function.injective (@π₁.change_of_basepoint _ _ (h.to_fun x₀) _ (u h)).to_monoid_hom,
      { exact mul_equiv.injective _ },
      rw [bij_helper₂, monoid_hom.coe_comp] at this,
      exact function.injective.of_comp this },
    { have : function.surjective 
        (@π₁.change_of_basepoint _ _ x₀ _ (homotopy.path h.left_inv.some.symm)).to_monoid_hom,
      { exact mul_equiv.surjective _ },
      rw [←bij_helper₁, monoid_hom.coe_comp] at this,
      exact function.surjective.of_comp this } },
  set r := mul_equiv.of_bijective _ hyp with hr,
  have hyp₂ : π₁.map h.to_fun = r.symm.to_monoid_hom.comp (r.to_monoid_hom.comp (π₁.map h.to_fun)),
  { rw [←monoid_hom.comp_assoc, mul_equiv.symm_to_monoid_hom_comp_to_monoid_hom, 
        monoid_hom.id_comp] },
  rw [hyp₂, monoid_hom.coe_comp],
  apply function.bijective.comp,
  { exact mul_equiv.bijective _ },
  { have : function.bijective 
        (@π₁.change_of_basepoint _ _ x₀ _ (homotopy.path h.left_inv.some.symm)).to_monoid_hom,
      { exact mul_equiv.bijective _ },
    convert this,
    rw [hr, ←bij_helper₁],
    refl }
end

lemma map_homotopy_to_monoid_hom {Y : Type _} [topological_space Y] (h : homotopy_equiv X Y) :
  (map_homotopy h).to_monoid_hom = @map _ _ x₀ _ _ (h : C(X, Y)) := rfl

end π₁
