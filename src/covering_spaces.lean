import topology.continuous_function.basic

structure covering_map (X Y : Type _) [topological_space X] [topological_space Y] :=
(to_fun : C(X, Y))
(V : set Y → set (set X))
(prop :
  -- For each `y`,
  ∀ y : Y, 
  -- we have an open neighbourhood `U` of `y`
    ∃ U : set Y, y ∈ U ∧ is_open U ∧
  -- such that the preimage of `U` is a collection
    (⋃ A ∈ V U, A) = to_fun ⁻¹' U ∧
  -- of disjoint sets
    (∀ A B ∈ V U, (A ∩ B : set X).nonempty → A = B) ∧
  -- where each one is mapped homeomorphically to `U`
    (∀ (A : set X), A ∈ V U → ∃ h : homeomorph A U, ∀ (x : X) (hx : x ∈ A), 
      to_fun x = h ⟨x, hx⟩))
