import covering_space.def

variables {X X' Y : Type _} [topological_space X] [topological_space X'] [topological_space Y] 

lemma is_open_f₀_eq_f₁ {p : C(X', X)} (hp : is_covering_map p) {f : C(Y, X)} {f₀ f₁ : C(Y, X')} 
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

lemma is_closed_f₀_eq_f₁ {p : C(X', X)} (hp : is_covering_map p) {f : C(Y, X)} {f₀ f₁ : C(Y, X')} 
  (hf₀ : p.comp f₀ = f) (hf₁ : p.comp f₁ = f) :
  is_closed {y | f₀ y = f₁ y} :=
begin
  rw is_closed_iff_nhds,
  intros y hy,
  let U := hp.U (f y),
  have h₀ : f₀ y ∈ p ⁻¹' U,
  { rw [set.mem_preimage, ←p.comp_apply, hf₀],
    exact hp.mem_U _ },
  have h₁ : f₁ y ∈ p ⁻¹' U,
  { rw [set.mem_preimage, ←p.comp_apply, hf₁],
    exact hp.mem_U _ },
  rw [hp.preimage, set.mem_sUnion] at h₀ h₁,
  rcases ⟨h₀, h₁⟩ with ⟨⟨V₀, hV₀, hV₀'⟩, V₁, hV₁, hV₁'⟩,
  rcases hp.homeo (f y) V₀ hV₀ with ⟨p', hp'₀, hp'₁, hp'₂⟩,
  rcases hp.homeo (f y) V₁ hV₁ with ⟨q', hq'₀, hq'₁, hq'₂⟩,
  let N := f₀ ⁻¹' V₀ ∩ f₁ ⁻¹' V₁,
  have hNnhds : N ∈ nhds y,
  { rw mem_nhds_iff,
    refine ⟨N, set.subset.refl _, _, _⟩,
    { apply is_open.inter,
      { apply continuous.is_open_preimage f₀.continuous,
        rw ←hp'₀,
        exact p'.open_source },
      { apply continuous.is_open_preimage f₁.continuous,
        rw ←hq'₀,
        exact q'.open_source } },
    exact ⟨hV₀', hV₁'⟩ },
  rcases hy _ hNnhds with ⟨t, ⟨ht₀ : f₀ t ∈ V₀, ht₁ : f₁ t ∈ V₁⟩, ht₂ : f₀ t = f₁ t⟩,
  have hVeq := (hp.disj (f y)).elim hV₀ hV₁ (f₀ t) ht₀ (ht₂.symm ▸ ht₁),
  apply p'.inj_on _ _,
  { rw [hp'₂ _ hV₀', hp'₂ _ (hVeq.symm ▸ hV₁' : f₁ y ∈ V₀), ←p.comp_apply, ←p.comp_apply, hf₀, 
        hf₁] },
  { rwa hp'₀ },
  { rwa [hp'₀, hVeq] }
end

variable [connected_space Y]

lemma lift_unique (p : C(X', X)) (hp : is_covering_map p) (f : C(Y, X)) (f₀ f₁ : C(Y, X')) 
  (hf₀ : p.comp f₀ = f) (hf₁ : p.comp f₁ = f) (y₀ : Y) (hy₀ : f₀ y₀ = f₁ y₀) (y : Y) :
  f₀ y = f₁ y :=
begin
  let S := {y | f₀ y = f₁ y},
  suffices : S = set.univ,
  { rw set.eq_univ_iff_forall at this,
    exact this y },
  exact eq_univ_of_nonempty_clopen ⟨y₀, hy₀⟩ ⟨is_open_f₀_eq_f₁ hp hf₀ hf₁, is_closed_f₀_eq_f₁ hp hf₀ hf₁⟩,
end
