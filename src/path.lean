import topology.continuous_function.basic
import topology.instances.real

/-!
# Paths

Given a topological space `X`, and points `x₀ x₁ : X`, we define a `path' x₀ x₁` to be a continuous
function `to_fun : C(ℝ, X)` where `to_fun 0 = x₀` and `to_fun 1 = x₁`.

We define an API for a different version of paths as in mathlib (although it is possible to convert
between the two fairly easily), since the mathlib version has `I → ℝ`, which can sometimes be
unwieldy in our applications.
-/

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y]

/--
`path' x₀ x₁` is the type of all paths joining `x₀` and `x₁`.
-/
@[ext]
structure path' (x₀ x₁ : X) :=
(to_fun : C(ℝ, X))
(to_fun_zero' : to_fun 0 = x₀)
(to_fun_one' : to_fun 1 = x₁)

namespace path'

variables {x₀ x₁ x₂ : X} (p : path' x₀ x₁)

instance : has_coe (path' x₀ x₁) (C(ℝ, X)) := ⟨path'.to_fun⟩ 

@[continuity] lemma continuous {f : path' x₀ x₁} : continuous f := f.to_fun.continuous_to_fun

@[simp] lemma coe_apply (i : ℝ) : (p : C(ℝ, X)) i = p.to_fun i := rfl

@[simp] lemma to_fun_zero : p.to_fun 0 = x₀ := p.to_fun_zero'

@[simp] lemma to_fun_one : p.to_fun 1 = x₁ := p.to_fun_one'

/--
The image of a path under a continuous function is a path.
-/
def map (p : path' x₀ x₁) (f : C(X, Y)) : path' (f x₀) (f x₁) :=
{ to_fun := f.comp p.to_fun,
  to_fun_zero' := by simp,
  to_fun_one' := by simp }

@[simp] lemma to_fun_map (p : path' x₀ x₁) (f : C(X, Y)) : (p.map f).to_fun = f.comp p.to_fun :=
  rfl

/--
If `p₀` is a path from `x₀` to `x₁`, and `p₁` is a path from `x₁` to `x₂`, we can define a path
from `x₀` to `x₂` by joining them together.
-/
def trans (p₀ : path' x₀ x₁) (p₁ : path' x₁ x₂) : path' x₀ x₂ :=
{ to_fun := 
  { to_fun := λ s, if s ≤ 1/2 then p₀.to_fun (2 * s) else p₁.to_fun (2 * s - 1),
    continuous_to_fun := begin
      apply continuous.if; [rintros a (ha : a ∈ frontier (set.Iic (1/2 : ℝ))), continuity, continuity],
      simp * at *
    end },
  to_fun_zero' := by simp,
  to_fun_one' := by norm_num } .

@[simp] lemma map_trans (p₀ : path' x₀ x₁) (p₁ : path' x₁ x₂) (f : C(X, Y)) : 
  (p₀.trans p₁).map f = (p₀.map f).trans (p₁.map f) :=
begin
  ext,
  simp only [path'.to_fun_map,
              continuous_map.comp_coe,
              continuous_map.coe_mk,
              function.comp_app,
              path'.trans.equations._eqn_1],
  split_ifs; simp
end

/--
The constant path in `x`.
-/
def const (x : X) : path' x x :=
{ to_fun := 
  { to_fun := λ t, x },
  to_fun_zero' := by simp,
  to_fun_one' := by simp }

@[simp] lemma const_map (x : X) (f : C(X, Y)) : (const x).map f = const (f x) :=
begin
  ext,
  simp [const],
end

@[simp] lemma const_to_fun (x : X) (t : ℝ) : (const x).to_fun t = x := rfl 

/--
The inverse of a path is given by traversing the path in the opposite direction.
-/
def inv (p : path' x₀ x₁) : path' x₁ x₀ :=
{ to_fun := { to_fun := λ s, p.to_fun (1 - s) },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num }

end path'
