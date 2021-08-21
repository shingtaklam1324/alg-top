import topology.continuous_function.basic
import topology.local_homeomorph
import locally_path_connected

variables {X Y X' : Type _} [topological_space X] [topological_space Y] [topological_space X']

structure is_covering_map (p : Y → X) :=
(U : X → set X)
(is_open_U : ∀ x, is_open (U x))
(mem_U : ∀ x, x ∈ U x)
(cover : X → set (set Y))
(preimage : ∀ x, p ⁻¹' {x} = ⋃₀ (cover x))
(disj : ∀ x, (cover x).pairwise_disjoint)
(homeo : ∀ x, ∀ T ∈ cover x, ∃ (h : local_homeomorph X Y), h.source = U x ∧ h.target = T)

structure is_pointed_covering_map (p : Y → X) (x₀ : X) (y₀ : Y) extends is_covering_map p :=
(hy₀ : p y₀ = x₀)

def is_lift (f : Y → X) (p : X' → X) (f' : Y → X') := f = p ∘ f'

variables [connected_space Y] [locally_path_connected_space Y]

example (f : C(Y, X)) (p : X' → X) (hp : is_covering_map p) (f₁' f₂' : Y → X') (y₀ : Y) 
  (hy₀ : f₁' y₀ = f₂' y₀) (y : Y) : f₁' y = f₂' y :=
begin
  let S := {y | f₁' y = f₂' y},
  have hSnonempty : S.nonempty := ⟨y₀, hy₀⟩,
  let U := hp.U (f y₀),
  obtain ⟨V, hV₀, hV₁, hV₂⟩ := locally_path_connected_space.path_connected y₀ (f ⁻¹' U) _ _,
  rotate,
  { rw set.mem_preimage,
    exact hp.mem_U _ },
  { exact continuous.is_open_preimage f.continuous _ (hp.is_open_U _) },
end
