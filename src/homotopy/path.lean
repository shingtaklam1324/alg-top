import homotopy.basic
import topology.path_connected
import path.defs
import intervals

/-!
# Homotopy of Paths

In this file, we define what it means for two paths to be homotopic. Furthermore, we show that this
is an equivalence relation.
-/

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y] {x₀ x₁ x₂ x₃ : X}

open_locale unit_interval

/--
A `path_homotopy` between paths `f₀` and `f₁` is a homotopy between `f₀` and `f₁` which keep the end
points fixed.
-/
abbreviation path_homotopy (f₀ f₁ : path' x₀ x₁) := 
  homotopy_with (f₀ : C(ℝ, X)) f₁ (λ r, r 0 = x₀ ∧ r 1 = x₁)

namespace path_homotopy

section lemmas

variables {f₀ f₁ : path' x₀ x₁}

@[simp] lemma to_fun_zero (h : path_homotopy f₀ f₁) {t : ℝ} : 
  h (0, t) = x₀ :=
by simpa using (h.prop t).1

@[simp] lemma to_fun_one (h : path_homotopy f₀ f₁) {t : ℝ} : 
  h (1, t) = x₁ :=
by simpa using (h.prop t).2

/--
A path is homotopic to itself.
-/
def refl (f₀ : path' x₀ x₁) : path_homotopy f₀ f₀ := homotopy_with.refl (by simp)

/--
Given two paths `f₀` and `f₁` which agree for all inputs, we have a homotopy between them.
-/
def of_refl {f₀ f₁ : path' x₀ x₁} (h : f₀ = f₁) : path_homotopy f₀ f₁ := 
{ to_fun := 
  { to_fun := λ p : ℝ × ℝ, f₀ (prod.fst p) },
  to_fun_zero' := by simp [h],
  to_fun_one' := by simp [h],
  prop := by simp [h] }

/--
If `f₀` and `f₁` are homotopic paths, and `F` is a continuous function, then the images of the paths
are homotopic.
-/
def map (h : path_homotopy f₀ f₁) (F : C(X, Y)) : path_homotopy (f₀.map F) (f₁.map F) :=
{ to_fun := F.comp h,
  to_fun_zero' := by simp,
  to_fun_one' := by simp,
  prop := λ t, by simp } .

/--
A path `f₀` is homotopic to `f₀` joined to the constant path.
-/
def trans_const (f₀ : path' x₀ x₁)  : path_homotopy f₀ (f₀.trans (path'.const x₁)) :=
{ to_fun := 
  { to_fun := λ p, f₀ (if p.1 ≤ 1/2 then (1 + p.2) * p.1 else (1 - p.2) * p.1 + p.2),
    continuous_to_fun := begin
      apply continuous.comp,
      { continuity },
      apply continuous.if; [skip, continuity, continuity],
      { intros a ha,
        rw mem_frontier_fst_le at ha,
        rw ha,
        linarith },
    end },
  to_fun_zero' := by norm_num,
  to_fun_one' := λ t, begin
    simp only [path'.trans, one_div, path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, 
               path'.const_to_fun, continuous_map.coe_mk, zero_mul, zero_add, mul_zero, sub_self, 
               neg_zero],
    split_ifs; norm_num,
  end,
  prop := λ t, by norm_num } .

/--
A path `f₀` is homotopic to `f₀` joined to the constant path.
-/
def const_trans (f₀ : path' x₀ x₁)  : path_homotopy f₀ ((path'.const x₀).trans f₀) :=
{ to_fun := 
  { to_fun := λ p, f₀ (if p.1 ≤ 1/2 then (1 - p.2) * p.1 else (1 + p.2) * p.1 - p.2),
    continuous_to_fun := begin
      apply continuous.comp,
      { continuity },
      apply continuous.if; [skip, continuity, continuity],
      { intros a ha,
        rw mem_frontier_fst_le at ha,
        rw ha,
        linarith }
    end },
  to_fun_zero' := by norm_num,
  to_fun_one' := λ t, begin
    simp only [path'.trans, one_div, path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, 
               path'.const_to_fun, continuous_map.coe_mk, zero_mul, zero_add, neg_neg, mul_zero, 
               sub_self, neg_zero],
    split_ifs; norm_num,
  end,
  prop := λ t, by norm_num } .

/--
If `f₀` and `g₀` are homotopic, and `f₁` and `g₁` are homotopic, then `f₀` joined with `f₁` is
homotopic to `g₀` joined to `g₁`.
-/
def trans₂ {f₀ g₀ : path' x₀ x₁} {f₁ g₁ : path' x₁ x₂} (h₀ : path_homotopy f₀ g₀) (h₁ : path_homotopy f₁ g₁) :
  path_homotopy (f₀.trans f₁) (g₀.trans g₁) :=
{ to_fun := 
  { to_fun := λ p, if p.1 ≤ 1/2 then h₀ (2 * p.1, p.2) else h₁ (2 * p.1 - 1, p.2),
    continuous_to_fun := begin
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw mem_frontier_fst_le at ha,
      norm_num [ha],
    end },
  to_fun_zero' := by simp [path'.trans],
  to_fun_one' := by simp [path'.trans],
  prop := λ t, by norm_num } .

/--
If `f` and `g` are homotopic paths, then their inverses are also homotopic.
-/
def inv {f g : path' x₀ x₁} (h : path_homotopy f g) : path_homotopy f.inv g.inv :=
{ to_fun := 
  { to_fun := λ p, h (1 - p.1, p.2) },
  to_fun_zero' := by norm_num [path'.inv],
  to_fun_one' := by norm_num [path'.inv],
  prop := by norm_num [path'.inv] }

end lemmas

section assoc

private def δ (γ₀ : path' x₀ x₁) (γ₁ : path' x₁ x₂) (γ₂ : path' x₂ x₃) : C(ℝ, X) :=
{ to_fun := λ t, 
  if t ≤ 1/3 then
    γ₀ (3 * t)
  else if t ≤ 2/3 then
    γ₁ (3 * t - 1)
  else
    γ₂ (3 * t - 2),
  continuous_to_fun := begin
    apply continuous.if; [rintros a (ha : a ∈ frontier (set.Iic (1/3 : ℝ))), continuity, skip],
    { rw [frontier_Iic, set.mem_singleton_iff] at ha,
      norm_num [ha] },
    { apply continuous.if; [rintros b (hb : b ∈ frontier (set.Iic (2/3 : ℝ))), continuity, continuity],
      { rw [frontier_Iic, set.mem_singleton_iff] at hb,
        norm_num [hb] } } 
  end } .

private def f₀ : path' (0 : ℝ) 1 :=
{ to_fun := 
  { to_fun := λ t, if t ≤ 1/2 then 4/3 * t else 1/3 + 2/3 * t,
    continuous_to_fun := begin
      apply continuous.if; [rintros a (ha : a ∈ frontier (set.Iic (1/2 : ℝ))), continuity, continuity],
      rw [frontier_Iic, set.mem_singleton_iff] at ha,
      norm_num [ha]
    end },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num }

private def f₁ : path' (0 : ℝ) 1 :=
{ to_fun := 
  { to_fun := λ t, if t ≤ 1/2 then 2/3 * t else -1/3 + 4/3 * t,
    continuous_to_fun := begin
      apply continuous.if; [rintros a (ha : a ∈ frontier (set.Iic (1/2 : ℝ))), continuity, continuity],
      rw [frontier_Iic, set.mem_singleton_iff] at ha,
      norm_num [ha],
    end },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num }

private def path_homotopy_f₀_f₁ : path_homotopy f₀ f₁ :=
{ to_fun := 
  { to_fun := λ p, if p.1 ≤ 1/2 then 2/3 * p.1 * (2 - p.2) else 1/3 + 2/3 * p.1 - 2/3 * p.2 + 2/3 * p.1 * p.2,
    continuous_to_fun := begin
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw mem_frontier_fst_le at ha,
      rw ha,
      linarith,
    end },
  to_fun_zero' := λ x, begin
    simp only [f₀, one_div, path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, 
               continuous_map.coe_mk, sub_zero, zero_add, neg_neg, mul_zero, neg_zero],
    split_ifs; linarith
  end,
  to_fun_one' := λ x, begin
    simp only [f₁, path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, 
               continuous_map.coe_mk, zero_add, neg_neg, mul_zero, neg_zero],
    split_ifs; linarith
  end,
  prop := λ t, by norm_num }

variables {γ₀ : path' x₀ x₁} {γ₁ : path' x₁ x₂} {γ₂ : path' x₂ x₃}

private lemma f₀_map_δ_eq : ((f₀.map (δ γ₀ γ₁ γ₂)) : ℝ → X) = ((γ₀.trans γ₁).trans γ₂) :=
begin
  ext t,
  unfold f₀ δ path'.trans,
  simp only [δ, path'.map, path'.coe_apply, path'.mk_apply, continuous_map.comp_coe, 
             continuous_map.coe_mk, function.comp_app, mul_ite],
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈;
    [apply congr_arg, exfalso, exfalso, apply congr_arg, exfalso, exfalso, exfalso, exfalso, 
     apply congr_arg]; linarith
end .

private lemma f₁_map_δ_eq : (f₁.map (δ γ₀ γ₁ γ₂) : ℝ → X) = (γ₀.trans (γ₁.trans γ₂)) :=
begin
  ext t,
  unfold f₁ δ path'.trans,
  simp only [δ, path'.map, path'.coe_apply, path'.mk_apply, continuous_map.comp_coe, 
             continuous_map.coe_mk, function.comp_app, mul_ite],
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈;
    [apply congr_arg, exfalso, exfalso, exfalso, exfalso, apply congr_arg, exfalso, exfalso, 
     apply congr_arg]; linarith,
end

/--
When dealing with `path_homotopy`s, sometimes we end up in a case where the end points have a
different type from what we expect.

Consider for example if we had maps `f g : C(X, X)` such that `f x₀ = x₀` and `g x₁ = x₁`,
(which can be proven, but is not true "by definition"). Then say if we had a homotopy between 
`p : path' x₀ x₁` and `q : path' x₀ x₁`, we can use this to define a homotopy between
`p' : path' (f x₀) (g x₁)` and `q' : path' (f x₀) (g x₁)`, where `p'` as a function is the same
as `p`, and `q'` as a function is the same as `q`.
-/
def change_end_points {x₁ x₂ y₁ y₂ : X} {f₁ f₂ : path' x₁ x₂} {g₁ g₂ : path' y₁ y₂} 
  (h : path_homotopy f₁ f₂) (hfg₁ : (f₁ : ℝ → X) = g₁) (hfg₂ : (f₂ : ℝ → X) = g₂) : 
  path_homotopy g₁ g₂ :=
{ to_fun := h,
  to_fun_zero' := by simp [←hfg₁],
  to_fun_one' := by simp [←hfg₂],
  prop := λ t, begin
    simp only [to_fun_one, to_fun_zero, homotopy_with.coe_coe_apply_eq_coe],
    split,
    { simp [←f₁.to_fun_zero, hfg₁, g₁.to_fun_zero] },
    { simp [←f₁.to_fun_one, hfg₁, g₁.to_fun_one] },
  end }

/--
If we have paths `γ₀`, `γ₁` and `γ₂`, then the two paths formed by joined them in different ways
are different, but there is a homotopy between them.
-/
def assoc : path_homotopy ((γ₀.trans γ₁).trans γ₂) (γ₀.trans (γ₁.trans γ₂)) :=
  (path_homotopy_f₀_f₁.map (δ γ₀ γ₁ γ₂)).change_end_points f₀_map_δ_eq f₁_map_δ_eq

end assoc

section inv

variable {f : path' x₀ x₁}

/--
A path joined to it's inverse is homotopic to the constant path.
-/
def trans_right_inv : path_homotopy (f.trans f.inv) (path'.const x₀) :=
{ to_fun := 
  { to_fun := λ p, f (if p.1 ≤ 1/2 then 2 * p.1 * (1 - p.2) else (1 - p.2) * (2 - 2 * p.1)),
    continuous_to_fun := begin
      apply continuous.comp; [continuity, skip],
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw mem_frontier_fst_le at ha,
      rw ha,
      linarith,
    end },
  to_fun_zero' := λ x, begin
    unfold path'.trans path'.inv,
    simp only [path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, continuous_map.coe_mk, 
               sub_zero, zero_add, neg_neg, neg_zero],
    split_ifs; apply congr_arg; linarith
  end,
  to_fun_one' := by norm_num,
  prop := λ t, by norm_num }

/--
A path joined to it's inverse is homotopic to the constant path.
-/
def trans_left_inv : path_homotopy (f.inv.trans f) (path'.const x₁) :=
{ to_fun := 
  { to_fun := λ p, f (if p.1 ≤ 1/2 then (1 - p.2) * (1 - 2 * p.1) + p.2 else (1 - p.2) * (2 * p.1 - 1) + p.2),
    continuous_to_fun := begin
      apply continuous.comp; [continuity, skip],
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw mem_frontier_fst_le at ha,
      rw ha,
      linarith,
    end },
  to_fun_zero' := λ x, begin
    unfold path'.trans path'.inv,
    simp only [path'.coe_apply, add_zero, mul_one, one_mul, path'.mk_apply, continuous_map.coe_mk, 
               zero_mul, sub_zero, zero_add, mul_zero, neg_zero],
    split_ifs; apply congr_arg; linarith
  end,
  to_fun_one' := by norm_num,
  prop := λ t, by norm_num }

end inv

end path_homotopy

/--
Two paths are homotopic if there exists a homotopy between them.
-/
def path_homotopic (f₀ f₁ : path' x₀ x₁) := nonempty (path_homotopy f₀ f₁)

lemma path_homotopic.equiv : equivalence (@path_homotopic X _ x₀ x₁) :=
⟨λ p, ⟨path_homotopy.refl p⟩, λ f g ⟨h⟩, ⟨h.symm⟩, λ f₀ f₁ f₂ ⟨h₀⟩ ⟨h₁⟩, ⟨h₀.trans h₁⟩⟩
