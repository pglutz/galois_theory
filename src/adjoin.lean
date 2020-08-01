import field_theory.subfield
import ring_theory.algebra
import group_theory.subgroup
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import ring_theory.adjoin_root
import data.zmod.basic

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

def adjoin : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin_contains_field (x : F) : algebra_map F E x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

instance : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin_contains_field F S x⟩}

lemma adjoin_contains_element (x : S) : ↑x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    right,
    exact subtype.mem x,
end

instance adjoin.is_subfield : is_subfield (adjoin F S) := field.closure.is_subfield

instance adjoin.has_scalar : has_scalar F (adjoin F S) := {
    smul := λ x y, ⟨algebra_map F E x, adjoin_contains_field F S x⟩ * y,
}

instance adjoin.is_algebra : algebra F (adjoin F S) := {
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

variables (α : E) (h : is_integral F α)

def adjoin_simple : set E := adjoin F {α}

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

--generator of F(α)
def adjoin_simple.gen : (adjoin_simple F α) := ⟨α, adjoin_simple_contains_element F α⟩

lemma adjoin_simple.gen_eq_alpha : algebra_map (adjoin_simple F α) E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple.composition : (algebra_map F E) = (algebra_map (adjoin_simple F α) E).comp (algebra_map F (adjoin_simple F α)) :=
begin
    ext,
    refl,
end

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


noncomputable def algebra_equiv_of_bij_hom {A : Type*} [ring A] [algebra F A] {B : Type*} [ring B] [algebra F B] (f : A →ₐ[F] B) (h : function.bijective f) : A ≃ₐ[F] B :=
{ .. f, .. equiv.of_bijective _ h }

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

def to_adjunction_embedding_equalizer : set (adjoin_simple F α) :=
(λ f, ι f = to_adjunction_embedding F α h ι f)

instance to_adjunction_embedding_equalizer_is_subfield : is_subfield (to_adjunction_embedding_equalizer F α h ι) := {
    zero_mem :=
    begin
        change ι 0 = to_adjunction_embedding F α h ι 0,
        rw alg_hom.map_zero,
        rw alg_hom.map_zero,
    end,
    add_mem :=
    begin
        intros a b ha hb,
        change ι a = to_adjunction_embedding F α h ι a at ha,
        change ι b = to_adjunction_embedding F α h ι b at hb,
        change ι (a + b) = to_adjunction_embedding F α h ι (a + b),
        rw alg_hom.map_add,
        rw alg_hom.map_add,
        rw ha,
        rw hb,
    end,
    neg_mem :=
    begin
        intros a ha,
        change ι a = to_adjunction_embedding F α h ι a at ha,
        change ι (-a) = to_adjunction_embedding F α h ι (-a),
        rw alg_hom.map_neg,
        rw alg_hom.map_neg,
        rw ha,
    end,
    one_mem :=
    begin
        change ι 1 = to_adjunction_embedding F α h ι 1,
        rw alg_hom.map_one,
        rw alg_hom.map_one,
    end,
    mul_mem :=
    begin
        intros a b ha hb,
        change ι a = to_adjunction_embedding F α h ι a at ha,
        change ι b = to_adjunction_embedding F α h ι b at hb,
        change ι (a * b) = to_adjunction_embedding F α h ι (a * b),
        rw alg_hom.map_mul,
        rw alg_hom.map_mul,
        rw ha,
        rw hb,
    end,
    inv_mem :=
    begin
        intros a ha,
        change (ι : (adjoin_simple F α) →+* E') a = (to_adjunction_embedding F α h ι : (adjoin_simple F α) →+* E') a at ha,
        change (ι : (adjoin_simple F α) →+* E') a⁻¹ = (to_adjunction_embedding F α h ι : (adjoin_simple F α) →+* E') a⁻¹,
        rw ring_hom.map_inv,
        rw ring_hom.map_inv,
        rw ha,
    end
}

--proves that every map F(α) → E' is comes from adjunction_embedding
lemma adjunction_embedding_classification : ι = to_adjunction_embedding F α h ι :=
begin
    
end