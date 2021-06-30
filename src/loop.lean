import path

variables {X : Type _} [topological_space X]

abbreviation loop (x : X) := path' x x
