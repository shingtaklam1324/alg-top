import path.defs

/-!
# Loops

In this file we define loops as paths with the same start and end points.
-/

variables {X : Type _} [topological_space X]

/--
A `loop x` is a `path' x x`.
-/
abbreviation loop (x : X) := path' x x
