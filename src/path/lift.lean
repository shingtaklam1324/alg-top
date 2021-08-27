import covering_space.lift
import locally_path_connected
import path.defs

variables {X X' Y : Type _} [topological_space X] [topological_space X'] [topological_space Y]
variables {x₀ x₁ : X}

example (p : C(X', X)) (hp : is_covering_map p) (γ : path' x₀ x₁) (x₀' : X') (hx₀' : p x₀' = x₀) : 
  is_open {t ∈ set.Icc (0 : ℝ) 1 | ∃ γ' : C(ℝ, X'), (∀ w ∈ set.Icc (0 : ℝ) t, γ w = (p.comp γ') w) ∧ γ' 0 = x₀'} :=
begin
  rw is_open_iff_forall_mem_open,
  rintros t₀ ⟨ht₀, γ', hγ'₀, hγ'₁⟩,
  let U := hp.U (γ t₀),
  dsimp,
end
