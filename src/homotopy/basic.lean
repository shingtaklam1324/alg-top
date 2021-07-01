import topology.continuous_function.basic
import topology.instances.real
import topology.path_connected
import intervals

/-!
# Homotopy

In this file, we define homotopies between continuous functions. Note in particular that we are
defining homotopies to be `to_fun : C(X × ℝ, Y)` instead of `to_fun : C(X × I, Y)`. This is because
of the subtypes can be annoying to work with, and we don't actually care about the value that the
homotopy takes outside of `X × [0, 1]`.

## Implementation Notes

The definition of homotopies is inspired by the file HOL-Library/Homotopy, by Lawrence Paulson. In
particular, we define a general `homotopy_with f₀ f₁ P`, which is a homotopy between `f₀` and `f₁`,
where all of the intermediate maps satisfy the property `P`. In particular, this general definition
allows us to define homotopy, homotopy between paths, homotopy between loops and homotopy relative
to a subset all using the same definition. 

## Key Declarations

- `homotopy_with f₀ f₁ P` - A homotopy between `f₀` and `f₁`, where all of the intermediate maps
  satisfy the property `P`.
- `homotopy f₀ f₁` - A homotopy between `f₀` and `f₁`.
-/

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y]

/--
A homotopy between `f₀` and `f₁`, with a proposition `P` restricting the intermediate maps.
-/
@[nolint has_inhabited_instance] -- if `P` is always `false`, then there are no homotopies.
structure homotopy_with (f₀ f₁ : C(X, Y)) (P : (X → Y) → Prop) :=
(to_fun : C(X × ℝ, Y))
(to_fun_zero' : ∀ x, to_fun (x, 0) = f₀ x)
(to_fun_one' : ∀ x, to_fun (x, 1) = f₁ x)
(prop : ∀ t, P(λ x, to_fun (x, t)))

namespace homotopy_with

variables {f₀ f₁ f₂ : C(X, Y)} {P : (X → Y) → Prop}

instance : has_coe_t (homotopy_with f₀ f₁ P) (C(X × ℝ, Y)) := ⟨homotopy_with.to_fun⟩
instance : has_coe_to_fun (homotopy_with f₀ f₁ P) := ⟨_, λ h, h.to_fun.to_fun⟩

@[continuity]
lemma continuous (h : homotopy_with f₀ f₁ P) : continuous h := h.to_fun.continuous

@[simp] lemma to_fun_zero (h : homotopy_with f₀ f₁ P) (x : X) : h (x, 0) = f₀ x := 
  h.to_fun_zero' x 

@[simp] lemma to_fun_one (h : homotopy_with f₀ f₁ P) (x : X) : h (x, 1) = f₁ x := 
  h.to_fun_one' x 

@[simp] lemma coe_coe_apply_eq_coe (h : homotopy_with f₀ f₁ P) (x : X × ℝ) :
  (h : C(X × ℝ, Y)) x = h x := rfl

/--
If `f₀` satisfies the property `P`, then we have a `homotopy_with f₀ f₀ P`.
-/
def refl (hP : P f₀) : homotopy_with f₀ f₀ P :=
{ to_fun := 
  { to_fun := λ p, f₀ p.1 },
  to_fun_zero' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  to_fun_one' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  prop := λ t, hP }

/--
If `f₀` and `f₁` agree on every input, and that `f₀` satisfies the property `P`, then we have a ` homotmotopy_with f₀ f₁ P`.
-/
def of_refl (hP : P f₀) (h : f₀ = f₁) : homotopy_with f₀ f₁ P :=
{ to_fun := { to_fun := λ p, f₀ p.1 },
  to_fun_zero' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  to_fun_one' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true, h],
  prop := λ t, hP }

/--
If we have `h : homotopy_with f₀ f₁ P`, we can define a `homotopy_with f₁ f₀ P` by reversing the 
direction of the homotopy.
-/
def symm (h : homotopy_with f₀ f₁ P) : homotopy_with f₁ f₀ P :=
{ to_fun := 
  { to_fun := λ p, h (p.1, 1 - p.2) },
  to_fun_zero' := by simp,
  to_fun_one' := by simp,
  prop := λ t, 
  begin
    simp only [continuous_map.coe_mk],
    apply h.prop,
  end }

/--
If we have `h₀ : homotopy_with f₀ f₁ P` and `h₁ : homotopy_with f₁ f₂ P`, we can define a
`homotopy_with f₀ f₂ P` by 'gluing' the homotopies together.
-/
def trans (h₀ : homotopy_with f₀ f₁ P) (h₁ : homotopy_with f₁ f₂ P) : homotopy_with f₀ f₂ P :=
{ to_fun := 
  { to_fun := λ p, if p.2 ≤ 1/2 then h₀ (p.1, 2 * p.2) else h₁ (p.1, 2 * p.2 - 1),
    continuous_to_fun := begin
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw frontier_snd_le at ha,
      obtain ⟨ha₁, ha₂⟩ := ha,
      simp only [*, one_div, set.mem_singleton_iff, to_fun_one, mul_inv_cancel, ne.def, 
                 not_false_iff, bit0_eq_zero, one_ne_zero, to_fun_zero, sub_self] at *,
    end },
  to_fun_zero' := λ x, by simp only [one_div, zero_le_one, inv_nonneg, if_true, 
                                     continuous_map.coe_mk, zero_le_bit0, to_fun_zero, mul_zero],
  to_fun_one' := λ x, by norm_num,
  prop := λ t, begin
    simp only [continuous_map.coe_mk, set.mem_singleton_iff, to_fun_one, mul_inv_cancel, 
               ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, to_fun_zero, sub_self],
    split_ifs,
    { apply h₀.prop },
    { apply h₁.prop }
  end }

end homotopy_with

/--
A `homotopy f₀ f₁` is defined to be a `homotopy_with f₀ f₁ P`, where `P` is always `true`.
-/
abbreviation homotopy (f₀ f₁ : C(X, Y)) := homotopy_with f₀ f₁ (λ f, true)

namespace homotopy

variables {f₀ f₁ f₂ : C(X, Y)}

/--
For `homotopy f₀ f₀`, the property `P` in `homotopy_with.refl` is always satisfied, so we add in
this definition so we don't need to prove `true` every time. 
-/
def refl (f₀ : C(X, Y)) : homotopy f₀ f₀ := homotopy_with.refl trivial

/--
The property `P` in `homotopy_with.refl` is always satisfied for `homotopy`, so we add in this
definition so we don't need to prove `true` every time.
-/
def of_refl (h : f₀ = f₁) : homotopy f₀ f₁ := homotopy_with.of_refl trivial h

end homotopy

/--
Two continuous functions `f₀` and `f₁` are homotopic if there exists a `homotopy f₀ f₁`.
-/
def homotopic (f₀ f₁ : C(X, Y)) := nonempty (homotopy f₀ f₁)

lemma homotopic.equiv : equivalence (@homotopic X Y _ _) :=
⟨λ f, ⟨homotopy.refl f⟩, λ f g ⟨h⟩, ⟨h.symm⟩, λ f₀ f₁ f₂ ⟨h₀⟩ ⟨h₁⟩, ⟨h₀.trans h₁⟩⟩
