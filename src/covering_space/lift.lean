import covering_space.def
import locally_path_connected

variables {X X' Y : Type _} [topological_space X] [topological_space X'] [topological_space Y] 

lemma is_open_ (p : C(X', X)) (hp : is_covering_map p) (f : C(Y, X)) (f₀ f₁ : C(Y, X')) 
  (hf₀ : p.comp f₀ = f) (hf₁ : p.comp f₁ = f) :
  is_open {y | f₀ y = f₁ y} :=
begin
  let S := {y | f₀ y = f₁ y},
  rw is_open_iff_forall_mem_open,
  rintros y (hy : f₀ y = f₁ y),
  let U := hp.U (f y),
  let Vs := hp.cover (f y),
  have : f₀ y ∈ p ⁻¹' U,
  { rw [set.mem_preimage, ←p.comp_apply, hf₀],
    exact hp.mem_U _ },
  rw [hp.preimage, set.mem_sUnion] at this,
  rcases this with ⟨W, hW₁, hW₂⟩,
  let N := f₀ ⁻¹' W ∩ f₁ ⁻¹' W,
  rcases hp.homeo (f y) W hW₁ with ⟨p', hp'₀, hp'₁, hp'₂⟩,
  refine ⟨N, _, _, _⟩,
  { intros n hn,
    show f₀ n = f₁ n,
    have h₀ : f₀ n ∈ W := hn.1,
    have h₁ : f₁ n ∈ W := hn.2,
    apply p'.inj_on _ _,
    { rw [hp'₂ (f₀ n) ‹_›, hp'₂ (f₁ n) ‹_›, ←p.comp_apply, ←p.comp_apply, hf₀, hf₁] },
    { rwa hp'₀ },
    { rwa hp'₀ } },
  have hWopen : is_open W,
  { rw ←hp'₀,
    exact p'.open_source },
  { apply is_open.inter,
    { apply continuous.is_open_preimage f₀.continuous,
      exact hWopen },
    { apply continuous.is_open_preimage f₁.continuous,
      exact hWopen } },
  { refine ⟨hW₂, _⟩,
    rwa [set.mem_preimage, ←hy] }
end

lemma is_closed_ (p : C(X', X)) (hp : is_covering_map p) (f : C(Y, X)) (f₀ f₁ : C(Y, X')) 
  (hf₀ : p.comp f₀ = f) (hf₁ : p.comp f₁ = f) :
  is_closed {y | f₀ y = f₁ y} :=
begin
  rw is_closed_iff_nhds,
  intros y hy,
  by_contra h,
  change f₀ y ≠ f₁ y at h,
  let U := hp.U (f y),
  sorry
end
