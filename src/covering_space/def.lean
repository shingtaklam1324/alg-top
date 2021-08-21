import topology.continuous_function.basic
import topology.local_homeomorph
import locally_path_connected

variables {X Y X' : Type _} [topological_space X] [topological_space Y]

structure is_covering_map (p : C(Y, X)) :=
(U : X → set X)
(is_open_U : ∀ x, is_open (U x))
(mem_U : ∀ x, x ∈ U x)
(cover : X → set (set Y))
(preimage : ∀ x, p ⁻¹' (U x) = ⋃₀ (cover x))
(disj : ∀ x, (cover x).pairwise_disjoint)
(homeo : ∀ x, ∀ T ∈ cover x, ∃ (p' : local_homeomorph Y X), p'.source = T ∧ p'.target = U x ∧ ∀ x ∈ T, p' x = p x)

structure is_pointed_covering_map (p : C(Y, X)) (x₀ : X) (y₀ : Y) extends is_covering_map p :=
(hy₀ : p y₀ = x₀)
