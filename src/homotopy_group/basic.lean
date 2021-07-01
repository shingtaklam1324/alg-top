import homotopy.loop
import homotopy.tactic

/-!
# The Fundamental Group of a Topological Space

In this file, we define the fundamental group `π₁ x₀` of a topological space `X` based at `x₀`.
-/

noncomputable theory

variables {X : Type _} [topological_space X]

/--
For `x₀ : X`, `π₁ x₀` is the fundamental group of `X` based at `x₀`.
-/
@[nolint has_inhabited_instance] -- I think it might be always inhabited? But I'm not sure.
def π₁ (x₀ : X) := quotient (@loop.setoid _ _ x₀)

namespace π₁

variables {x₀ : X}

/--
Multiplication of elements in `π₁ x₀` is defined by joining the paths of an element of the
homotopy class.
-/
def mul (l₀ l₁ : π₁ x₀) : π₁ x₀ := quotient.lift₂ (λ l l' : loop x₀, quotient.mk (l.trans l')) 
  begin
    rintros p₁ p₂ q₁ q₂ ⟨h₁⟩ ⟨h₂⟩,
    simp only [quotient.eq],
    exact ⟨path_homotopy.trans₂ h₁ h₂⟩,
  end l₀ l₁

/--
The identity in `π₁ x₀` is the homotopy class of the coonstant path.
-/
def one : π₁ x₀ := quotient.mk (path'.const x₀)

/--
The inverse of an element `l` of `π₁ x₀` is defined by taking the inverse of an element of the
equivalence class.
-/
def inv (l : π₁ x₀) : π₁ x₀ := quotient.lift (λ l', quotient.mk (path'.inv l')) 
  begin
    rintros p₁ p₂ ⟨h₁⟩,
    simp only [quotient.eq],
    exact ⟨h₁.inv⟩,
  end l

instance : has_mul (π₁ x₀) := ⟨mul⟩
instance : has_one (π₁ x₀) := ⟨one⟩
instance : has_inv (π₁ x₀) := ⟨inv⟩

lemma mul_def (l₀ l₁ : loop x₀) : @has_mul.mul (π₁ x₀) _ (⟦l₀⟧ : π₁ x₀) ⟦l₁⟧ = ⟦l₀.trans l₁⟧ := rfl
lemma one_def : (1 : π₁ x₀) = ⟦path'.const x₀⟧ := rfl
lemma inv_def (l : loop x₀) : @has_inv.inv (π₁ x₀) _ ⟦l⟧ = ⟦path'.inv l⟧ := rfl

lemma mul_assoc (l₀ l₁ l₂ : π₁ x₀) : l₀ * l₁ * l₂ = l₀ * (l₁ * l₂) :=
quotient.induction_on₃ l₀ l₁ l₂ (λ p₀ p₁ p₂, begin 
    simp only [mul_def, quotient.eq],
    exact ⟨path_homotopy.assoc⟩,
  end)

lemma one_mul (l : π₁ x₀) : 1 * l = l :=
quotient.induction_on l (λ p, begin
    simp only [one_def, mul_def, quotient.eq],
    exact ⟨(path_homotopy.const_trans p).symm⟩,
  end)

lemma mul_one (l : π₁ x₀) : l * 1 = l :=
quotient.induction_on l (λ p, begin
    simp only [one_def, mul_def, quotient.eq],
    exact ⟨(path_homotopy.trans_const p).symm⟩,
  end)

lemma mul_left_inv (l : π₁ x₀) : l⁻¹ * l = 1 :=
quotient.induction_on l (λ p, begin
    simp [one_def, mul_def, inv_def],
    refine ⟨path_homotopy.trans_left_inv⟩,
  end)

/--
The `group` instance for `π₁ x₀`.
-/
instance : group (π₁ x₀) := 
{ mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_left_inv := mul_left_inv,
  ..π₁.has_mul, ..π₁.has_inv, ..π₁.has_one }

section defs

open path_homotopy.tactic

/--
Given a path `α` from `x₀` to `x₁`, we can define a group isomorphism from `π₁ x₀` to `π₁ x₁`.
-/
def change_of_basepoint {x₀ x₁ : X} (α : path' x₀ x₁) : π₁ x₀ ≃* π₁ x₁ :=
{ to_fun := quotient.lift (λ l, ⟦(α.inv.trans l).trans α⟧) begin
    rintros a b ⟨h⟩,
    rw quotient.eq,
    exact ⟨path_homotopy.trans₂ 
      (path_homotopy.trans₂ (path_homotopy.refl _) h) (path_homotopy.refl _)⟩,
  end,
  inv_fun := quotient.lift (λ l, ⟦(α.trans l).trans α.inv⟧) begin
    rintros a b ⟨h⟩,
    rw quotient.eq,
    refine 
      ⟨path_homotopy.trans₂ (path_homotopy.trans₂ (path_homotopy.refl _) h) (path_homotopy.refl _)⟩,
  end,
  left_inv := begin
    intro l,
    apply quotient.induction_on l,
    intro p,
    rw [quotient.lift_mk, quotient.lift_mk, quotient.eq],
    refine ⟨homotopy_with.trans 
      (homotopy_with.trans _ (path_homotopy.trans₂ (@path_homotopy.trans_right_inv _ _ _ _ α) 
        (path_homotopy.trans₂ (path_homotopy.refl _) (@path_homotopy.trans_right_inv _ _ _ _ α)))) 
        (homotopy_with.trans (path_homotopy.trans_const _) (path_homotopy.const_trans _)).symm⟩,
    assocl, assocr',
    refine path_homotopy.trans₂ (path_homotopy.refl _) _,
    assocl, assocl,
    exact path_homotopy.refl _,
  end,
  right_inv := begin
    intro l,
    apply quotient.induction_on l,
    intro p,
    rw [quotient.lift_mk, quotient.lift_mk, quotient.eq],
    refine ⟨homotopy_with.trans 
      (homotopy_with.trans _ (path_homotopy.trans₂ (@path_homotopy.trans_left_inv _ _ _ _ α) 
        (path_homotopy.trans₂ (path_homotopy.refl _) (@path_homotopy.trans_left_inv _ _ _ _ α)))) 
        (homotopy_with.trans (path_homotopy.trans_const _) (path_homotopy.const_trans _)).symm⟩,
    assocl, assocr',
    refine path_homotopy.trans₂ (path_homotopy.refl _) _,
    assocl, assocl,
    refine path_homotopy.trans₂ (path_homotopy.refl _) _,
    exact path_homotopy.refl _,
  end,
  map_mul' := begin
    intros x y,
    apply quotient.induction_on₂ x y,
    intros p q,
    rw [mul_def, quotient.lift_mk, quotient.lift_mk, quotient.lift_mk, mul_def, quotient.eq],
    exact ⟨homotopy_with.trans (path_homotopy.trans₂ (homotopy_with.trans 
      (homotopy_with.trans path_homotopy.assoc.symm (path_homotopy.trans₂ (homotopy_with.trans 
        (homotopy_with.trans (path_homotopy.trans_const _) 
      (path_homotopy.trans₂ 
        (path_homotopy.refl _) path_homotopy.trans_right_inv.symm)) path_homotopy.assoc.symm) 
        (path_homotopy.refl _))) 
        path_homotopy.assoc) 
      (path_homotopy.refl _)) path_homotopy.assoc⟩,
  end }

/--
Given a continuous function `f : C(X, Y)`, we have a group homomorphism from `π₁ x₀` to `π₁ (f x₀)`.
-/
def map {Y : Type _} [topological_space Y] (f : C(X, Y)) : π₁ x₀ →* π₁ (f x₀) :=
{ to_fun := quotient.lift (λ l, ⟦path'.map l f⟧) begin
    rintros a b ⟨h⟩,
    rw [quotient.eq],
    exact ⟨h.map _⟩,
  end,
  map_one' := begin
    rw [one_def, one_def, quotient.lift_mk, quotient.eq],
    exact ⟨path_homotopy.of_refl (path'.const_map _ _)⟩,
  end,
  map_mul' := begin
    intros x y,
    apply quotient.induction_on₂ x y,
    intros p q,
    rw [mul_def, quotient.lift_mk, quotient.lift_mk, quotient.lift_mk, mul_def, quotient.eq],
    refine ⟨path_homotopy.of_refl (path'.map_trans _ _ _)⟩,
  end } .

lemma map_comp {Y Z : Type _} [topological_space Y] [topological_space Z] (h : C(X, Y)) (k : C(Y, Z)) :
  @map _ _ x₀ _ _ (k.comp h) = (map k).comp (map h) :=
begin
  ext t,
  apply quotient.induction_on t,
  intro a,
  simp [map],
end

@[simp] lemma map_id : 
  @map _ _ x₀ _ _ continuous_map.id = monoid_hom.id _ :=
begin
  ext t,
  apply quotient.induction_on t,
  intro a,
  simp only [map, path'.map, quotient.lift_mk, monoid_hom.id_apply, monoid_hom.coe_mk, quotient.eq],
  refine ⟨path_homotopy.of_refl _⟩,
  ext u,
  refl,
end

end defs

section path_connected

variable [path_connected_space X] 

/--
In a path connected space `X`, for `x₀ x₁ : X`, `π₁ x₀` and `π₁ x₁` are isomorphic.
-/
noncomputable def mul_equiv_of_path_connected (x₀ x₁ : X) : 
  π₁ x₀ ≃* π₁ x₁ :=
change_of_basepoint (path'.of_path (path_connected_space.some_path x₀ x₁))

end path_connected

end π₁
