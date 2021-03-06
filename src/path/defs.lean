import topology.continuous_function.basic
import topology.instances.real
import topology.path_connected

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

instance : has_coe_t (path' x₀ x₁) (C(ℝ, X)) := ⟨path'.to_fun⟩ 
instance : has_coe_to_fun (path' x₀ x₁) := ⟨_, λ p, p.to_fun.to_fun⟩

@[continuity] lemma continuous {f : path' x₀ x₁} : continuous f := f.to_fun.continuous_to_fun

/--
Converting a `path` to a `path'`.
-/
def of_path (q : path x₀ x₁) : path' x₀ x₁ :=
{ to_fun := { to_fun := set.Icc_extend zero_le_one q },
  to_fun_zero' := by simp,
  to_fun_one' := by simp }

@[simp] lemma coe_apply (i : ℝ) : (p : C(ℝ, X)) i = p i := rfl

@[simp] lemma to_fun_zero : p 0 = x₀ := p.to_fun_zero'

@[simp] lemma to_fun_one : p 1 = x₁ := p.to_fun_one'

/--
Converting a `path'` to a `path`. Note that this is a left inverse to `of_path`, but it is *not*
a right inverse.
-/
def to_path : path x₀ x₁ :=
{ to_fun := λ t, p t,
  continuous' := by continuity,
  source' := by simp,
  target' := by simp }

/--
The image of a path under a continuous function is a path.
-/
def map (p : path' x₀ x₁) (f : C(X, Y)) : path' (f x₀) (f x₁) :=
{ to_fun := f.comp p,
  to_fun_zero' := by simp,
  to_fun_one' := by simp }

@[simp] lemma map_apply (p : path' x₀ x₁) (f : C(X, Y)) (t : ℝ) : 
  (p.map f) t = (f.comp (p : C(ℝ, X))) t := rfl

@[simp] lemma mk_apply (f : C(ℝ, X)) {h₁} {h₂} (t : ℝ) : (⟨f, h₁, h₂⟩ : path' x₀ x₁) t = f t := rfl

/--
If `p₀` is a path from `x₀` to `x₁`, and `p₁` is a path from `x₁` to `x₂`, we can define a path
from `x₀` to `x₂` by joining them together.
-/
def trans (p₀ : path' x₀ x₁) (p₁ : path' x₁ x₂) : path' x₀ x₂ :=
{ to_fun := 
  { to_fun := λ s, if s ≤ 1/2 then p₀ (2 * s) else p₁ (2 * s - 1),
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
  simp only [trans, map, one_div, mk_apply, continuous_map.comp_coe, continuous_map.coe_mk, 
             function.comp_app, coe_apply],
  split_ifs; refl
end

@[simp] lemma map_comp {Z : Type _} [topological_space Z] (p : path' x₀ x₁) (f : C(X, Y)) (g : C(Y, Z)) :
  (p.map f).map g = p.map (g.comp f) := rfl

/--
The constant path in `x`.
-/
def const (x : X) : path' x x :=
{ to_fun := 
  { to_fun := λ t, x },
  to_fun_zero' := by simp,
  to_fun_one' := by simp }

@[simp] lemma const_map (x : X) (f : C(X, Y)) : (const x).map f = const (f x) := rfl

@[simp] lemma const_to_fun (x : X) (t : ℝ) : (const x) t = x := rfl 

/--
The inverse of a path is given by traversing the path in the opposite direction.
-/
def inv (p : path' x₀ x₁) : path' x₁ x₀ :=
{ to_fun := { to_fun := λ s, p (1 - s) },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num }

end path'
