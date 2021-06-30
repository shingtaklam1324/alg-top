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
-/

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y]

/--
A homotopy between `f₀` and `f₁`, with a proposition `P` restricting the intermediate maps.
-/
structure homotopy_with (f₀ f₁ : C(X, Y)) (P : (X → Y) → Prop) :=
(to_fun : C(X × ℝ, Y))
(to_fun_zero' : ∀ x, to_fun (x, 0) = f₀ x)
(to_fun_one' : ∀ x, to_fun (x, 1) = f₁ x)
(prop : ∀ t, P(λ x, to_fun (x, t)))

namespace homotopy_with

variables {f₀ f₁ f₂ : C(X, Y)} {P : (X → Y) → Prop}

@[simp] lemma to_fun_zero (h : homotopy_with f₀ f₁ P) (x : X) : h.to_fun (x, 0) = f₀ x := 
  h.to_fun_zero' x 
@[simp] lemma to_fun_one (h : homotopy_with f₀ f₁ P) (x : X) : h.to_fun (x, 1) = f₁ x := 
  h.to_fun_one' x 

def refl (hP : P f₀) : homotopy_with f₀ f₀ P :=
{ to_fun := 
  { to_fun := λ p, f₀ p.1 },
  to_fun_zero' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  to_fun_one' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  prop := λ t, hP }

def of_refl (hP : P f₀) (h : f₀ = f₁) : homotopy_with f₀ f₁ P :=
{ to_fun := { to_fun := λ p, f₀ p.1 },
  to_fun_zero' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true],
  to_fun_one' := by simp only [continuous_map.coe_mk, implies_true_iff, eq_self_iff_true, h],
  prop := λ t, hP }

def symm (h : homotopy_with f₀ f₁ P) : homotopy_with f₁ f₀ P :=
{ to_fun := 
  { to_fun := λ p, h.to_fun ⟨p.1, 1 - p.2⟩ },
  to_fun_zero' := 
    by simp,
  to_fun_one' := 
    by simp,
  prop := λ t, 
  begin
    simp only [continuous_map.coe_mk],
    apply h.prop,
  end }

def trans (h₀ : homotopy_with f₀ f₁ P) (h₁ : homotopy_with f₁ f₂ P) : homotopy_with f₀ f₂ P :=
{ to_fun := 
  { to_fun := λ p, if p.2 ≤ 1/2 then h₀.to_fun (p.1, 2 * p.2) else h₁.to_fun (p.1, 2 * p.2 - 1),
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

abbreviation homotopy (f₀ f₁ : C(X, Y)) := homotopy_with f₀ f₁ (λ f, true)

namespace homotopy

variables {f₀ f₁ f₂ : C(X, Y)}

def refl (f₀ : C(X, Y)) : homotopy f₀ f₀ := homotopy_with.refl trivial

end homotopy

def homotopic (f₀ f₁ : C(X, Y)) := nonempty (homotopy f₀ f₁)

lemma homotopic.equiv : equivalence (@homotopic X Y _ _) :=
⟨λ f, ⟨homotopy.refl f⟩, λ f g ⟨h⟩, ⟨h.symm⟩, λ f₀ f₁ f₂ ⟨h₀⟩ ⟨h₁⟩, ⟨h₀.trans h₁⟩⟩

@[refl]
lemma homotopic.refl {f : C(X, Y)} : homotopic f f := homotopic.equiv.1 f

@[symm]
lemma homotopic.symm {f g : C(X, Y)} : homotopic f g → homotopic g f := λ h, homotopic.equiv.2.1 h
