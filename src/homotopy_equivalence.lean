import homotopy

section homotopy_equivalence
variables (X Y : Type _) [topological_space X] [topological_space Y]

structure homotopy_equivalence :=
(to_fun : C(X, Y))
(inv_fun : C(Y, X))
(left_inv : homotopic (inv_fun.comp to_fun) continuous_map.id)
(right_inv : homotopic (to_fun.comp inv_fun) continuous_map.id)

def homotopy_equivalent := nonempty (homotopy_equivalence X Y)

end homotopy_equivalence
