import path.loop
import homotopy.path
import homotopy.straight_line

/-!
# Homotopy of Loops

In this file we define what it means for two `loop`s to be homotopic, and show that this is an
equivalence relation.
-/

noncomputable theory

variables {X : Type _} [topological_space X] {x₀ : X}

abbreviation loop_homotopy (l₀ l₁ : loop x₀) := path_homotopy l₀ l₁

def loop_homotopic (l₀ l₁ : loop x₀) := nonempty (loop_homotopy l₀ l₁)

lemma loop_homotopic.equiv : equivalence (@loop_homotopic _ _ x₀) := path_homotopic.equiv

instance loop.setoid : setoid (loop x₀) :=
{ r := loop_homotopic,
  iseqv := loop_homotopic.equiv }
