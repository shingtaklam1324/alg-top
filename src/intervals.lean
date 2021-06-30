import topology.instances.real

/-!
# Some helpful lemmas for (products of) intervals.
-/

variables {X : Type _} [topological_space X]

lemma frontier_snd_le (a : ℝ) : frontier {x : X × ℝ | x.snd ≤ a} = (set.univ : set X).prod {a} :=
calc frontier {x : X × ℝ | x.snd ≤ a} 
      = frontier ((set.univ : set X).prod (set.Iic a)) : 
        congr_arg _ $ by { ext, simp }
  ... = (set.univ : set X).prod {a} : 
        by rw [frontier_univ_prod_eq, frontier_Iic]

lemma mem_frontier_snd_le (a : ℝ) (y : X × ℝ) : y ∈ frontier {x : X × ℝ | x.snd ≤ a} ↔ y.2 = a :=
begin
  rw frontier_snd_le,
  split,
  { rintros ⟨-, ha⟩,
    rwa set.mem_singleton_iff at ha },
  { intro ha,
    split,
    { simp },
    { simp [ha] } }
end

lemma frontier_fst_le (a : ℝ) : frontier {x : ℝ × X | x.fst ≤ a} = ({a} : set ℝ).prod (set.univ) :=
calc frontier {x : ℝ × X | x.fst ≤ a} 
      = frontier ((set.Iic a).prod set.univ) : congr_arg _ $ by { ext, simp }
  ... = ({a} : set ℝ).prod (set.univ) : by rw [frontier_prod_univ_eq, frontier_Iic]

lemma mem_frontier_fst_le (a : ℝ) (y : ℝ × X) : y ∈ frontier {x : ℝ × X | x.fst ≤ a} ↔ y.1 = a :=
begin
  rw frontier_fst_le,
  split,
  { rintros ⟨ha, -⟩,
    rwa set.mem_singleton_iff at ha },
  { intro ha,
    split,
    { simp [ha] },
    { simp } }
end
