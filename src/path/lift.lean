import covering_space.lift
import path.defs

variables {X X' Y : Type _} [topological_space X] [topological_space X'] [topological_space Y]
variables {x₀ x₁ : X}

example (p : C(X', X)) (hp : is_covering_map p) (γ : path' x₀ x₁) (x₀' : X') (hx₀' : p x₀' = x₀) : 
  is_open {t | }
