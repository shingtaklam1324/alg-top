import topology.continuous_function.basic

variables {X : Type _} [topological_space X] {x : X}

@[simp] lemma id_coe : (continuous_map.id : X → X) = id := rfl

example : continuous_map.id x = x := by simp
