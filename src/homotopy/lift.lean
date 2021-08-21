import homotopy.basic
import covering_space.lift

variables {X X' Y : Type _} [topological_space X] [topological_space X'] [topological_space Y] 

open_locale unit_interval

example (p : C(X', X)) (hp : is_covering_map p) (f₀ f₁ : C(Y, X)) (H : homotopy f₀ f₁) (f₀' : C(Y, X'))
  (hf₀' : p.comp f₀' = f₀) : C(Y × I, X) :=
sorry
