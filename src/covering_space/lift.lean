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

section

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

end

-- example (p : C(X', X)) (hp : is_covering_map p) (h : C(Y × ℝ, X)) (f₀ : C(Y, X')) (heq : ∀ y, h (y, 0) = p (f₀ y)) :
--   ∃ k : C(Y × ℝ, X'), (∀ y, k (y, 0) = f₀ y) ∧ (∀ z, h z = p (k z)) :=
-- begin
--   have : ∀ y, ∃ (V : set Y) (k : C(Y × ℝ, X')), is_open V ∧ y ∈ V ∧ (∀ z ∈ V, k (z, 0) = f₀ z) ∧ (∀ z, h z = p (k z)),
--   {  }
-- end

example (p : C(X', X)) (hp : is_covering_map p) (x₀' : X') (x₀ : X) (hp₀ : p x₀' = x₀) (f : C(ℝ, X)) 
  (hf : f 0 = x₀) : true :=
begin
  -- First, we obtain an open cover of X
  let Us := set.range hp.U,
  have hUopen : ∀ U ∈ Us, is_open U,
  { rintro U ⟨t, rfl⟩,
    exact hp.is_open_U _ },
  -- The preimage of each of the sets will be an open cover of ℝ
  let Vs := (λ t, f ⁻¹' t) '' Us,
  have hVopen : ∀ V ∈ Vs, is_open V,
  { rintro V ⟨U, hU₁, rfl⟩,
    exact f.continuous.is_open_preimage U (hUopen _ hU₁) },
  have hVcover : ⋃₀ Vs = set.univ,
  { rw set.eq_univ_iff_forall,
    intros x,
    let U := hp.U (f x),
    let V := f ⁻¹' U,
    refine ⟨V, ⟨U, ⟨f x, rfl⟩, rfl⟩, hp.mem_U _⟩ },
  -- Using the Lebesgue number lemma, we have some ε > 0 such that intervals of length < ε 
  -- (contained in I) are contained in some element of `Vs`
  let I : set ℝ := set.Icc 0 1,
  have hIcompact : is_compact I := is_compact_Icc,
  rcases lebesgue_number_lemma_sUnion hIcompact hVopen (hVcover.symm ▸ set.subset_univ _) with 
    ⟨n, hnunif, hn⟩,
  rw metric.mem_uniformity_dist at hnunif,
  rcases hnunif with ⟨ε, hεpos, hε⟩,
  -- Let k = 1/(N + 1) < ε. 
  rcases exists_nat_one_div_lt hεpos with ⟨N, hN⟩,
  -- Then note that each [nk, (n + 1)k] is contained in some element of `Vs`
end
