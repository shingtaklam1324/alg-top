import analysis.convex.basic
import homotopy.basic

noncomputable theory

variables {X : Type _} [topological_space X] 
-- todo: check if `topological_space E` or `normed_space E` makes more sense.
variables {E : Type _} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]

def straight_line_homotopy (f₀ f₁ : C(X, E)) : homotopy f₀ f₁ :=
{ to_fun := 
  { to_fun := λ p, (1 - p.2) • f₀ p.1 + p.2 • f₁ p.1 },
  to_fun_zero' := by norm_num,
  to_fun_one' := by norm_num,
  prop := λ _, trivial } .
