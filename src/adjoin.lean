import subfield_stuff
import group_theory.subgroup
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import ring_theory.adjoin_root
import data.zmod.basic

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

def adjoin : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin.mono (T : set E) (h : S ⊆ T) : adjoin F S ⊆ adjoin F T :=
begin
    apply field.closure_mono,
    apply set.union_subset,
    apply set.subset_union_left,
    apply set.subset_union_of_subset_right,
    exact h,
end 

lemma adjoin_contains_field (x : F) : algebra_map F E x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin_contains_field F S x⟩}

lemma adjoin_contains_field_set : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
    intros x hx,
    cases hx with f hf,
    rw ←hf,
    exact adjoin_contains_field F S f,
end

lemma adjoin_contains_field_subset {F : set E} {HF : is_subfield F} {T : set E} {HT : T ⊆ F} : T ⊆ adjoin F S :=
begin
    intros x hx,
    exact adjoin_contains_field F S ⟨x,HT hx⟩,
end

lemma adjoin_contains_field_as_subfield (F : set E) {HF : is_subfield F} : F ⊆ adjoin F S :=
λ x hx, adjoin_contains_field F S ⟨x, hx⟩

lemma adjoin_contains_element (x : S) : ↑x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    right,
    exact subtype.mem x,
end

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨↑x, adjoin_contains_element F S x⟩}

lemma adjoin_contains_set : S ⊆ adjoin F S :=
begin
    intros x hx,
    exact adjoin_contains_element F S ⟨x,hx⟩,
end

lemma adjoin_contains_subset {T : set E} {H : T ⊆ S} : T ⊆ adjoin F S :=
begin
    intros x hx,
    exact adjoin_contains_element F S ⟨x,H hx⟩,
end

instance adjoin.is_subfield : is_subfield (adjoin F S) := field.closure.is_subfield

instance adjoin.is_algebra : algebra F (adjoin F S) := {
    smul := λ x y, ⟨algebra_map F E x, adjoin_contains_field F S x⟩ * y,
    to_fun := λ x, ⟨algebra_map F E x, adjoin_contains_field F S x⟩,
    map_one' :=
    begin
        simp only [ring_hom.map_one],
        refl,
    end,
    map_mul' :=
    begin
        intros x y,
        simp only [ring_hom.map_mul],
        refl,
    end,
    map_zero' :=
    begin
        simp only [ring_hom.map_zero],
        refl,
    end,
    map_add' :=
    begin
        intros x y,
        simp only [ring_hom.map_add],
        refl,
    end,
    commutes' :=
    begin
        intros x y,
        rw mul_comm,
    end,
    smul_def' :=
    begin
        intros x y,
        refl,
    end
}

def adjoin_as_submodule : submodule F E := {
    carrier := adjoin F S,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ a b, is_add_submonoid.add_mem,
    smul_mem' :=
    begin
        intros a b hb,
        rw algebra.smul_def,
        exact is_submonoid.mul_mem (adjoin_contains_field F S a) hb,
    end
}

definition adjoin_as_submodule_equiv : (adjoin F S) ≃ₗ[F] (adjoin_as_submodule F S) := {
    to_fun := λ x, x,
    map_add' := λ x y, rfl,
    map_smul' :=
    begin
        intros x y,
        ext1,
        change _ = x • ↑y,
        rw algebra.smul_def,
        rw algebra.smul_def,
        refl,
    end,
    inv_fun := λ x, x,
    left_inv := λ x, rfl,
    right_inv := λ x, rfl,
}

lemma adjoin_subset {T : set E} [is_subfield T] (HF : set.range (algebra_map F E) ⊆ T) (HS : S ⊆ T) : adjoin F S ⊆ T :=
begin
    apply field.closure_subset,
    rw set.union_subset_iff,
    exact ⟨HF,HS⟩,
end

/-- If S ⊆ T then F[S] ⊆ F[T] -/
lemma adjoin_subset' {T : set E} (HT : S ⊆ adjoin F T) : adjoin F S ⊆ adjoin F T :=
adjoin_subset F S (adjoin_contains_field_set F T) HT

lemma set_range_subset {T₁ T₂ : set E} [is_subfield T₁] [is_subfield T₂] {hyp : T₁ ⊆ T₂} :
set.range (algebra_map T₁ E) ⊆ T₂ :=
begin
    intros x hx,
    cases hx with f hf,
    rw ←hf,
    cases f with t ht,
    exact hyp ht,
end

/- The range of the embedding of F into E is equal to the range of the inclusion embedding of
    range(F → E) into E. -/
lemma algebra_map_twice : set.range (algebra_map (set.range (algebra_map F E)) E) = set.range (algebra_map F E) :=
begin
    have : is_subfield (set.range (algebra_map F E)) := range.is_subfield (algebra_map F E),
    ext, split,
    {   rintros ⟨⟨y, ⟨z, rfl⟩⟩, rfl⟩,
        exact ⟨z, rfl⟩,
    },
    {   exact λ hx, ⟨⟨x, hx⟩, rfl⟩, },
end

/- Adjoining S to F is the same as adjoining S to the range of the embedding of F into E. -/
lemma adjoin_equals_adjoin_range : adjoin F S = adjoin (set.range (algebra_map F E)) S :=
by simp only [adjoin, algebra_map_twice]

lemma adjoin_twice (T : set E) : adjoin (adjoin F S) T = adjoin F (S ∪ T) :=
begin
    apply set.eq_of_subset_of_subset,
    apply adjoin_subset,
    apply set_range_subset,
    apply adjoin_subset,
    apply adjoin_contains_field_set,
    apply adjoin_contains_subset,
    apply set.subset_union_left,
    apply adjoin_contains_subset,
    apply set.subset_union_right,
    apply adjoin_subset,
    transitivity adjoin F S,
    apply adjoin_contains_field_set,
    apply adjoin_subset,
    apply adjoin_contains_field_subset,
    apply adjoin_contains_field_set,
    apply adjoin_contains_field_subset,
    apply adjoin_contains_set,
    apply set.union_subset,
    apply adjoin_contains_field_subset,
    apply adjoin_contains_set,
    apply adjoin_contains_set,
end

lemma adjoin.composition : (algebra_map F E) = (algebra_map (adjoin F S) E).comp (algebra_map F (adjoin F S)) :=
begin
    ext,
    refl,
end

instance adjoin_algebra_tower : is_algebra_tower F (adjoin F S) E := {
    smul_assoc :=
    begin
        intros x y z,
        rw algebra.smul_def,
        rw algebra.smul_def,
        rw algebra.smul_def,
        rw ring_hom.map_mul,
        rw mul_assoc,
        refl,
    end
}

variables (α : E) (h : is_integral F α)

def adjoin_simple : set E := adjoin F {α}

-- Let's try out this notation?
notation K`[`β`]` := adjoin_simple K β
notation K`[`β `,` γ`]` := adjoin K {β, γ}
-- This notation would allow us to write F[α, β] for adjoin_simple (adjoin_simple F α) β
-- notation K`⟨`L:(foldr `,` (x M, adjoin_simple M x) K `⟩`) := L 

lemma adjoin_simple_contains_field (x : F) : algebra_map F E x ∈ (adjoin_simple F α) :=
adjoin_contains_field F {α} x

instance : has_coe_t F (adjoin_simple F α) :=
{coe := λ x, ⟨algebra_map F E x, adjoin_simple_contains_field F α x⟩}

lemma adjoin_simple_contains_element : α ∈ adjoin_simple F α :=
adjoin_contains_element F {α} (⟨α,set.mem_singleton α⟩ : ({α} : set E))

instance adjoin_simple.is_subfield : is_subfield (adjoin_simple F α) :=
adjoin.is_subfield F {α}

instance adjoin_is_algebra : algebra F (adjoin_simple F α) :=
adjoin.is_algebra F {α}

def adjoin_simple_as_submodule : submodule F E :=
adjoin_as_submodule F {α}

definition adjoin_simple_as_submodule_equiv : (adjoin_simple F α) ≃ₗ[F] (adjoin_simple_as_submodule F α) :=
adjoin_as_submodule_equiv F {α}

/-- Adjoining α to F is the same as adjoining α to the range of the embedding of F into E. -/
lemma adjoin_simple_equals_adjoin_simple_range (α : E) : adjoin_simple F α = adjoin_simple (set.range (algebra_map F E)) α :=
adjoin_equals_adjoin_range F {α}

/-- A subfield of E that contains F and α also contains F[α] -/
lemma adjoin_simple_subset {T : set E} [is_subfield T] (HF : set.range (algebra_map F E) ⊆ T) (Hα : α ∈ T) : adjoin_simple F α ⊆ T :=
adjoin_subset F {α} HF (set.singleton_subset_iff.mpr Hα)

/-- If α is in F[T] then F[α] ⊆ F[T] -/
lemma adjoin_simple_subset' {T : set E} (HT : α ∈ adjoin F T) : adjoin_simple F α ⊆ adjoin F T :=
adjoin_subset' F {α} (set.singleton_subset_iff.mpr HT)

--generator of F(α)
def adjoin_simple.gen : (adjoin_simple F α) := ⟨α, adjoin_simple_contains_element F α⟩

lemma adjoin_simple.gen_eq_alpha : algebra_map (adjoin_simple F α) E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_twice (β : E) : adjoin_simple (adjoin_simple F α) β = adjoin F {α,β} :=
begin
    dsimp [adjoin_simple],
    rw adjoin_twice,
    refl,
end

lemma adjoin_simple.composition : (algebra_map F E) = (algebra_map (adjoin_simple F α) E).comp (algebra_map F (adjoin_simple F α)) :=
adjoin.composition F {α}

instance adjoin_simple_algebra_tower : is_algebra_tower F (F[α]) E :=
adjoin_algebra_tower F {α}

variables {E' : Type*} [field E'] [algebra F E'] (α' : E') (hα' : (minimal_polynomial h).eval₂ (algebra_map F E') α' = 0)

noncomputable def quotient_embedding_ring_hom :
(adjoin_root (minimal_polynomial h)) →+* E' :=
adjoin_root.lift (algebra_map F E') α' hα'

noncomputable def quotient_embedding : (adjoin_root (minimal_polynomial h)) →ₐ[F] E' := {
    to_fun := (quotient_embedding_ring_hom F α h α' hα').to_fun,
    map_one' := (quotient_embedding_ring_hom F α h α' hα').map_one',
    map_mul' := (quotient_embedding_ring_hom F α h α' hα').map_mul',
    map_zero' := (quotient_embedding_ring_hom F α h α' hα').map_zero',
    map_add' := (quotient_embedding_ring_hom F α h α' hα').map_add',
    commutes' :=
    begin
        intro r,
        change (quotient_embedding_ring_hom F α h α' hα') r = _,
        exact adjoin_root.lift_of,
    end
}

@[simp] lemma quotient_embedding_of_field (f : F) : quotient_embedding F α h α' hα' f = algebra_map F E' f :=
begin
    change quotient_embedding_ring_hom F α h α' hα' f = algebra_map F E' f,
    exact adjoin_root.lift_of,
end

@[simp] lemma quotient_embedding_of_root : quotient_embedding F α h α' hα' (adjoin_root.root (minimal_polynomial h)) = α' :=
begin
    change quotient_embedding_ring_hom F α h α' hα' (adjoin_root.root (minimal_polynomial h)) = α',
    exact adjoin_root.lift_root,
end

noncomputable instance yes_its_a_field_but_lean_want_me_to_give_this_instance_a_name : field (adjoin_root (minimal_polynomial h)) :=
@adjoin_root.field F _ (minimal_polynomial h) (minimal_polynomial.irreducible h)

lemma adjoin_simple.eval_gen : polynomial.eval₂ (algebra_map F ↥(adjoin_simple F α)) (adjoin_simple.gen F α) (minimal_polynomial h) = 0 :=
begin
    ext,
    have eval := minimal_polynomial.aeval h,
    dsimp[polynomial.aeval] at eval,
    rw adjoin_simple.composition F α at eval,
    have h := polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F (adjoin_simple F α)) (algebra_map (adjoin_simple F α) E) (adjoin_simple.gen F α),
    rw adjoin_simple.gen_eq_alpha at h,
    rw ←h at eval,
    exact eval,
end

noncomputable def quotient_to_adjunction_algebra_hom : (adjoin_root (minimal_polynomial h)) →ₐ[F] (adjoin_simple F α) :=
quotient_embedding F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h)

noncomputable def quotient_to_adjunction : adjoin_root (minimal_polynomial h) ≃ₐ[F] adjoin_simple F α :=
algebra_equiv_of_bij_hom F (quotient_to_adjunction_algebra_hom F α h)
begin
    set f := (algebra_map (adjoin_simple F α) E).comp((quotient_to_adjunction_algebra_hom F α h) : (adjoin_root (minimal_polynomial h)) →+* (adjoin_simple F α)),
    split,
    apply ring_hom.injective,
    have inclusion : (set.range (algebra_map F E) ∪ {α}) ⊆ set.range(f),
    rw set.union_subset_iff,
    split,
    intros x hx,
    rw set.mem_range at hx,
    cases hx with y hy,
    rw ←hy,
    use y,
    dsimp[f,quotient_to_adjunction_algebra_hom],
    rw quotient_embedding_of_field F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h) y,
    refl,
    intros x hx,
    rw set.mem_singleton_iff at hx,
    rw hx,
    use adjoin_root.root (minimal_polynomial h),
    dsimp[f,quotient_to_adjunction_algebra_hom],
    rw quotient_embedding_of_root F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h),
    refl,
    have key : (adjoin_simple F α) ⊆ set.range(f) := field.closure_subset inclusion,
    intro x,
    specialize key (subtype.mem x),
    cases key with a ah,
    use a,
    ext1,
    assumption,
end

@[simp] lemma quotient_to_adjunction_of_field (f : F) : quotient_to_adjunction F α h f = f :=
quotient_embedding_of_field F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h) f

@[simp] lemma quotient_to_adjunction_of_root : quotient_to_adjunction F α h (adjoin_root.root (minimal_polynomial h)) = adjoin_simple.gen F α :=
quotient_embedding_of_root F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h)

noncomputable def adjunction_embedding : (adjoin_simple F α) →ₐ[F] E' :=
(quotient_embedding F α h α' hα').comp((quotient_to_adjunction F α h).symm)

@[simp] lemma adjunction_embedding_of_field (f : F) : adjunction_embedding F α h α' hα' f = algebra_map F E' f :=
begin
    dsimp[adjunction_embedding],
    rw ←quotient_to_adjunction_of_field,
    rw alg_equiv.symm_apply_apply,
    rw quotient_embedding_of_field,
end

@[simp] lemma adjunction_embedding_of_root : adjunction_embedding F α h α' hα' (adjoin_simple.gen F α) = α' :=
begin
    dsimp[adjunction_embedding],
    rw ←quotient_to_adjunction_of_root,
    rw alg_equiv.symm_apply_apply,
    rw quotient_embedding_of_root,
end

variables (ϕ ψ : (adjoin F S) →+* E')

def adjoin_equalizer : set (adjoin F S) :=
(λ f, ϕ f = ψ f)

instance to_adjunction_embedding_equalizer_is_subfield : is_subfield (adjoin_equalizer F S ϕ ψ) := {
    zero_mem :=
    begin
        change ϕ 0 = ψ 0,
        rw ring_hom.map_zero,
        rw ring_hom.map_zero,
    end,
    add_mem :=
    begin
        intros a b ha hb,
        change ϕ a = ψ a at ha,
        change ϕ b = ψ b at hb,
        change ϕ (a + b) = ψ (a + b),
        rw ring_hom.map_add,
        rw ring_hom.map_add,
        rw ha,
        rw hb,
    end,
    neg_mem :=
    begin
        intros a ha,
        change ϕ a = ψ a at ha,
        change ϕ (-a) = ψ (-a),
        rw ring_hom.map_neg,
        rw ring_hom.map_neg,
        rw ha,
    end,
    one_mem :=
    begin
        change ϕ 1 = ψ 1,
        rw ring_hom.map_one,
        rw ring_hom.map_one,
    end,
    mul_mem :=
    begin
        intros a b ha hb,
        change ϕ a = ψ a at ha,
        change ϕ b = ψ b at hb,
        change ϕ (a * b) = ψ (a * b),
        rw ring_hom.map_mul,
        rw ring_hom.map_mul,
        rw ha,
        rw hb,
    end,
    inv_mem :=
    begin
        intros a ha,
        change ϕ a = ψ a at ha,
        change ϕ a⁻¹ = ψ a⁻¹,
        rw ring_hom.map_inv,
        rw ring_hom.map_inv,
        rw ha,
    end
}

instance to_adjunction_embedding_equalizer_coe_is_subfield : is_subfield ((coe '' adjoin_equalizer F S ϕ ψ) : set E) := {
    zero_mem := ⟨0,⟨is_add_submonoid.zero_mem,rfl⟩⟩,
    add_mem :=
    begin
        intros a b ha hb,
        cases ha with a' ha',
        cases hb with b' hb',
        rw[←ha'.2,←hb'.2],
        exact ⟨a'+b',⟨is_add_submonoid.add_mem ha'.1 hb'.1,rfl⟩⟩,
    end,
    neg_mem :=
    begin
        intros a ha,
        cases ha with a' ha',
        rw ←ha'.2,
        exact ⟨-a',⟨is_add_subgroup.neg_mem ha'.1,rfl⟩⟩,
    end,
    one_mem := ⟨1,⟨is_submonoid.one_mem,rfl⟩⟩,
    mul_mem :=
    begin
        intros a b ha hb,
        cases ha with a' ha',
        cases hb with b' hb',
        rw[←ha'.2,←hb'.2],
        exact ⟨a'*b',⟨is_submonoid.mul_mem ha'.1 hb'.1,rfl⟩⟩,
    end,
    inv_mem :=
    begin
        intros a ha,
        cases ha with a' ha',
        rw ←ha'.2,
        exact ⟨a'⁻¹,⟨is_subfield.inv_mem ha'.1,rfl⟩⟩,
    end
}

lemma ring_hom_determined_by_generators (hF : ∀ f : F, ϕ f = ψ f) (hS : ∀ s : S, ϕ s = ψ s) : ϕ = ψ :=
begin
    suffices key : adjoin F S ⊆ coe '' adjoin_equalizer F S ϕ ψ,
    ext,
    specialize key (subtype.mem x),
    cases key with y hy,
    rw ←subtype.ext hy.2,
    exact hy.1,
    dsimp[adjoin],
    rw field.closure_subset_iff,
    rw set.union_subset_iff,
    split,
    intros x hx,
    cases hx with y hy,
    exact ⟨↑y,⟨hF y,hy⟩⟩,
    intros x hx,
    exact ⟨⟨x,adjoin_contains_element F S ⟨x,hx⟩⟩,⟨hS ⟨x,hx⟩,rfl⟩⟩,
end

variable (ι : (adjoin_simple F α) →ₐ[F] E') 

lemma adjunction_embedding_classification_aux : polynomial.eval₂ (algebra_map F E') (ι (adjoin_simple.gen F α)) (minimal_polynomial h) = 0 :=
begin
    have key2 : ((ι : adjoin_simple F α →+* E').comp(algebra_map F (adjoin_simple F α)) = algebra_map F E'),
    ext,
    simp only [alg_hom.coe_to_ring_hom, function.comp_app, ring_hom.coe_comp, alg_hom.commutes],
    rw ←key2,
    change polynomial.eval₂ ((ι : adjoin_simple F α →+* E').comp(algebra_map F (adjoin_simple F α))) ((ι : adjoin_simple F α →+* E') (adjoin_simple.gen F α)) (minimal_polynomial h) = 0,
    rw ←polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F (adjoin_simple F α)) (ι : adjoin_simple F α →+* E') (adjoin_simple.gen F α),
    rw adjoin_simple.eval_gen,
    simp only [alg_hom.coe_to_ring_hom, alg_hom.map_zero],
end

noncomputable def to_adjunction_embedding : (adjoin_simple F α →ₐ[F] E') :=
adjunction_embedding F α h (ι (adjoin_simple.gen F α)) (adjunction_embedding_classification_aux F α h ι)

--proves that every map F(α) → E' is comes from adjunction_embedding
lemma adjunction_embedding_classification : ι = to_adjunction_embedding F α h ι :=
begin
    have key := ring_hom_determined_by_generators F {α} (ι : adjoin_simple F α →+* E') (to_adjunction_embedding F α h ι : adjoin_simple F α →+* E'),
    have hF : ∀ f : F, ι f = to_adjunction_embedding F α h ι f,
    intro f,
    dsimp[to_adjunction_embedding],
    rw adjunction_embedding_of_field,
    exact alg_hom.commutes ι f,
    specialize key hF,
    rw ring_hom.ext_iff at key,
    rw alg_hom.ext_iff,
    apply key,
    intro s,
    have h' : (↑s : adjoin F {α}) = adjoin_simple.gen F α,
    ext,
    cases s with s hs,
    exact set.mem_singleton_iff.2 hs,
    rw h',
    dsimp[to_adjunction_embedding],
    rw adjunction_embedding_of_root,
end

/-lemma quotient_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
    sorry
end

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root (minimal_polynomial h))) = (minimal_polynomial h).nat_degree :=
begin
    sorry
end

lemma adjunction_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
    sorry
end

lemma adjunction_degree : (finite_dimensional.findim F (adjoin_simple F α)) = (minimal_polynomial h).nat_degree :=
begin
    have algequiv : adjoin_root (minimal_polynomial h) ≃ₐ[F] adjoin_simple F α := quotient_to_adjunction F α h,
    have linequiv : adjoin_root (minimal_polynomial h) ≃ₗ[F] adjoin_simple F α,
    fconstructor,
    exact algequiv.to_fun,
    exact algequiv.map_add,
    intro c,
    intro x,
    change algequiv (c * x) = ((algebra_map F (adjoin_simple F α) c) * (algequiv x)),
    rw[algequiv.map_mul,←algequiv.commutes],
    refl,
    exact algequiv.inv_fun,
    exact algequiv.left_inv,
    exact algequiv.right_inv,
    rw ← @linear_equiv.findim_eq F (adjoin_root (minimal_polynomial h)) _ _ _ (adjoin_simple F α) _ _ linequiv (quotient_degree_finite F α h),
    exact quotient_degree F α h,
end-/