import loop
import path_homotopy

/-!
# Homotopy of Loops and the Fundamental Group

In this file we define what it means for two `loop`s to be homotopic, show that this is an
equivalence relation, and show that the quotient has a group structure.
-/

noncomputable theory

variables {X : Type _} [topological_space X] {x₀ : X}

abbreviation loop_homotopy (l₀ l₁ : loop x₀) := path_homotopy l₀ l₁

def loop_homotopic (l₀ l₁ : loop x₀) := nonempty (loop_homotopy l₀ l₁)

lemma loop_homotopic.equiv : equivalence (@loop_homotopic _ _ x₀) := path_homotopic.equiv

instance loop.setoid : setoid (loop x₀) :=
{ r := loop_homotopic,
  iseqv := loop_homotopic.equiv }

def π₁ (x₀ : X) := quotient (@loop.setoid _ _ x₀)

namespace π₁

def mul (l₀ l₁ : π₁ x₀) : π₁ x₀ := quotient.lift₂ (λ l l' : loop x₀, quotient.mk (l.trans l')) 
  begin
    rintros p₁ p₂ q₁ q₂ ⟨h₁⟩ ⟨h₂⟩,
    simp only [quotient.eq],
    exact ⟨path_homotopy.trans₂ h₁ h₂⟩,
  end l₀ l₁

def one : π₁ x₀ := quotient.mk (path'.const x₀)

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

instance : group (π₁ x₀) := 
{ mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_left_inv := mul_left_inv,
  ..π₁.has_mul, ..π₁.has_inv, ..π₁.has_one }

end π₁
