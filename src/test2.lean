import instances.real_vector_space
import contractible.simply_connected

variables {ι : Type _} [fintype ι]

example : simply_connected (ι → ℝ) := infer_instance
