import homotopy.basic

/-!
# Homotopy Equivalence

In this file, we define homotopy equivalences between topological spaces `X` and `Y`.
-/

noncomputable theory

variables (X Y : Type _) [topological_space X] [topological_space Y]

/--
A `homotopy_equiv X Y` is a pair of functions `to_fun : C(X, Y)` and `inv_fun : C(Y, X)` such that
`to_fun.comp inv_fun` and `inv_fun.comp to_fun` are homotopic to `continuous_map.id`
-/
@[nolint has_inhabited_instance] -- not all spaces are homotopy equivalent to eachother.
structure homotopy_equiv :=
(to_fun : C(X, Y))
(inv_fun : C(Y, X))
(left_inv : homotopic (inv_fun.comp to_fun) continuous_map.id)
(right_inv : homotopic (to_fun.comp inv_fun) continuous_map.id)

namespace homotopy_equiv

variables {X Y}

instance : has_coe_t (homotopy_equiv X Y) (C(X, Y)) := ⟨homotopy_equiv.to_fun⟩
instance : has_coe_to_fun (homotopy_equiv X Y) := ⟨_, λ h, h.to_fun.to_fun⟩

/--
A homeomorphism is a homotopy equivalence.
-/
def of_homeomorph (h : homeomorph X Y) : homotopy_equiv X Y :=
{ to_fun := { to_fun := h },
  inv_fun := { to_fun := h.symm },
  left_inv := ⟨homotopy.of_refl (by { ext, simp [continuous_map.id_apply] })⟩,
  right_inv := ⟨homotopy.of_refl (by { ext, simp [continuous_map.id_apply] })⟩ } .

def symm (h : homotopy_equiv X Y) : homotopy_equiv Y X :=
{ to_fun := h.inv_fun,
  inv_fun := h.to_fun,
  left_inv := h.right_inv,
  right_inv := h.left_inv }

end homotopy_equiv

/--
Two topological spaces `X` and `Y` are homotopy equivalent if there exists a `homotopy_equiv X Y`.
-/
class homotopy_equivalent :=
(hequiv : nonempty (homotopy_equiv X Y))
