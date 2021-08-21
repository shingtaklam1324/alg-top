import topology.path_connected

class locally_path_connected_space (X : Type _) [topological_space X] :=
(path_connected : ∀ (x : X) (U : set X), x ∈ U → is_open U → ∃ V : set X, x ∈ V ∧ V ⊆ U ∧ is_path_connected V)
