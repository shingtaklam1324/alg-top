import homotopy
import topology.path_connected
import path
import intervals

noncomputable theory

variables {X Y : Type _} [topological_space X] [topological_space Y] {x₀ x₁ x₂ x₃ : X}

open_locale unit_interval

abbreviation path_homotopy (f₀ f₁ : path' x₀ x₁) := 
  homotopy_with (f₀ : C(ℝ, X)) f₁ (λ r, r 0 = x₀ ∧ r 1 = x₁)

namespace path_homotopy

section lemmas

variables {f₀ f₁ : path' x₀ x₁}

@[simp] lemma to_fun_zero (h : path_homotopy f₀ f₁) {t : ℝ} : 
  h.to_fun (0, t) = x₀ :=
begin
  have := (h.prop t).1,
  simpa using this,
end

@[simp] lemma to_fun_one (h : path_homotopy f₀ f₁) {t : ℝ} : 
  h.to_fun (1, t) = x₁ :=
begin
  have := (h.prop t).2,
  simpa using this,
end

def refl (f₀ : path' x₀ x₁) : path_homotopy f₀ f₀ := homotopy_with.refl (by simp)

def map (h : path_homotopy f₀ f₁) (f : C(X, Y)) : path_homotopy (f₀.map f) (f₁.map f) :=
{ to_fun := f.comp h.to_fun,
  to_fun_zero' := by simp,
  to_fun_one' := by simp,
  prop := λ t, by simp } .

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
    simp only [path'.coe_apply, if_congr, continuous_map.coe_mk, zero_mul, 
               path'.trans.equations._eqn_1, sub_self],
    split_ifs,
    { norm_num },
    { simp }
  end,
  prop := λ t, by norm_num } .

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
    simp only [path'.coe_apply, if_congr, continuous_map.coe_mk, zero_mul, 
               path'.trans.equations._eqn_1, sub_self],
    split_ifs,
    { simp },
    { norm_num }
  end,
  prop := λ t, by norm_num } .

def trans₂ {f₀ g₀ : path' x₀ x₁} {f₁ g₁ : path' x₁ x₂} (h₀ : path_homotopy f₀ g₀) (h₁ : path_homotopy f₁ g₁) :
  path_homotopy (f₀.trans f₁) (g₀.trans g₁) :=
{ to_fun := 
  { to_fun := λ p, if p.1 ≤ 1/2 then h₀.to_fun (2 * p.1, p.2) else h₁.to_fun (2 * p.1 - 1, p.2),
    continuous_to_fun := begin
      apply continuous.if; [skip, continuity, continuity],
      intros a ha,
      rw mem_frontier_fst_le at ha,
      norm_num [ha],
    end },
  to_fun_zero' := by simp [path'.trans],
  to_fun_one' := by simp [path'.trans],
  prop := λ t, by norm_num } .

def inv {f g : path' x₀ x₁} (h : path_homotopy f g) : path_homotopy f.inv g.inv :=
{ to_fun := 
  { to_fun := λ p, h.to_fun (1 - p.1, p.2) },
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
    simp only [f₀, path'.coe_apply, add_zero, mul_one, one_mul, continuous_map.coe_mk, sub_zero, 
               zero_add, neg_neg, mul_zero, neg_zero],
    split_ifs; linarith
  end,
  to_fun_one' := λ x, begin
    simp only [f₁, path'.coe_apply, add_zero, mul_one, one_mul, continuous_map.coe_mk, zero_add, 
               neg_neg, mul_zero, neg_zero],
    split_ifs; linarith
  end,
  prop := λ t, by norm_num }

variables {γ₀ : path' x₀ x₁} {γ₁ : path' x₁ x₂} {γ₂ : path' x₂ x₃}

private lemma f₀_map_δ_eq : (f₀.map (δ γ₀ γ₁ γ₂)).to_fun = ((γ₀.trans γ₁).trans γ₂).to_fun :=
begin
  ext t,
  unfold f₀ δ path'.trans,
  simp only [path'.to_fun_map, continuous_map.comp_coe, continuous_map.coe_mk, function.comp_app, δ],
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈;
    [apply congr_arg, exfalso, exfalso, apply congr_arg, exfalso, exfalso, exfalso, exfalso, 
     apply congr_arg]; linarith
end .

private lemma f₁_map_δ_eq : (f₁.map (δ γ₀ γ₁ γ₂)).to_fun = (γ₀.trans (γ₁.trans γ₂)).to_fun :=
begin
  ext t,
  unfold f₁ δ path'.trans,
  simp only [path'.to_fun_map, continuous_map.comp_coe, continuous_map.coe_mk, function.comp_app, δ],
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈;
    [apply congr_arg, exfalso, exfalso, exfalso, exfalso, apply congr_arg, exfalso, exfalso, 
     apply congr_arg]; linarith,
end

def double_swap {x₁ x₂ y₁ y₂ : X} {f₁ f₂ : path' x₁ x₂} {g₁ g₂ : path' y₁ y₂} (h : path_homotopy f₁ f₂)
  (hfg₁ : f₁.to_fun = g₁.to_fun) (hfg₂ : f₂.to_fun = g₂.to_fun) : path_homotopy g₁ g₂ :=
{ to_fun := h.to_fun,
  to_fun_zero' := by simp [←hfg₁],
  to_fun_one' := by simp [←hfg₂],
  prop := λ t, begin
    simp only [to_fun_one, to_fun_zero],
    split,
    { rw [←f₁.to_fun_zero, hfg₁, g₁.to_fun_zero] },
    { rw [←f₁.to_fun_one, hfg₁, g₁.to_fun_one] },
  end }

def assoc : path_homotopy ((γ₀.trans γ₁).trans γ₂) (γ₀.trans (γ₁.trans γ₂)) :=
  (path_homotopy_f₀_f₁.map (δ γ₀ γ₁ γ₂)).double_swap f₀_map_δ_eq f₁_map_δ_eq

end assoc

section inv

variable {f : path' x₀ x₁}

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
    simp only [path'.coe_apply, mul_one, one_mul, continuous_map.coe_mk, coe_fn_coe_base, zero_add, 
               mul_zero, neg_zero],
    split_ifs; apply congr_arg; linarith
  end,
  to_fun_one' := by norm_num,
  prop := λ t, by norm_num }

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
    simp only [path'.coe_apply, mul_one, one_mul, continuous_map.coe_mk, coe_fn_coe_base, zero_add, 
               mul_zero, neg_zero],
    split_ifs; apply congr_arg; linarith
  end,
  to_fun_one' := by norm_num,
  prop := λ t, by norm_num }

end inv

end path_homotopy

def path_homotopic (f₀ f₁ : path' x₀ x₁) := nonempty (path_homotopy f₀ f₁)

lemma path_homotopic.equiv : equivalence (@path_homotopic X _ x₀ x₁) :=
⟨λ p, ⟨path_homotopy.refl p⟩, λ f g ⟨h⟩, ⟨h.symm⟩, λ f₀ f₁ f₂ ⟨h₀⟩ ⟨h₁⟩, ⟨h₀.trans h₁⟩⟩
