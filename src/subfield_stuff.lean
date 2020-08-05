import ring_theory.algebra
import field_theory.subfield

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

instance : has_coe_t F (set.range (algebra_map F E)) :=
{coe := λ x, ⟨algebra_map F E x, ⟨x,rfl⟩⟩}

instance : is_subfield (set.range (algebra_map F E)) := {
    inv_mem := begin
        intros x hx,
        cases hx with f hf,
        use f⁻¹,
        rw ←hf,
        exact (algebra_map F E).map_inv f,
    end,
}

instance : algebra F (set.range (algebra_map F E)) := {
    smul := λ f e, f * e,
    to_fun := λ f, f,
    map_zero' :=
    begin
        ext1, unfold_coes, simp,
    end,
    map_add' :=
    begin
        intros f e,
        ext1, unfold_coes, simp,
    end,
    map_one' :=
    begin
        ext1, unfold_coes, simp,
    end,
    map_mul' :=
    begin
        intros f e,
        ext1, unfold_coes, simp,
    end,
    smul_def' :=
    begin
        intros f e,
        refl,
    end,
    commutes' :=
    begin
        intros f e,
        ext1, unfold_coes, simp[mul_comm],
    end,
}

definition inclusion_algebra_hom : F →ₐ[F] set.range (algebra_map F E) := {
    to_fun := λ f, f,
    map_zero' :=
    begin
        ext1, unfold_coes, simp,
    end,
    map_add' :=
    begin
        intros f f',
        ext1, unfold_coes, simp,
    end,
    map_one' :=
    begin
        ext1, unfold_coes, simp,
    end,
    map_mul' :=
    begin
        intros f f',
        ext1, unfold_coes, simp,
    end,
    commutes' :=
    begin
        intros r, refl,
    end,
}

noncomputable def algebra_equiv_of_bij_hom {A : Type*} [ring A] [algebra F A] {B : Type*} [ring B] [algebra F B] (f : A →ₐ[F] B) (h : function.bijective f) : A ≃ₐ[F] B :=
{ .. f, .. equiv.of_bijective _ h }

noncomputable def inclusion_isomorphism : F ≃ₐ[F] set.range (algebra_map F E) :=
algebra_equiv_of_bij_hom F (inclusion_algebra_hom F E)
begin
    split,
    apply ring_hom.injective ((inclusion_algebra_hom F E) : F →+* set.range (algebra_map F E)),
    intro e,
    cases e with e he,
    cases he with f hf,
    use f,
    ext1,
    unfold_coes,
    simp,
    exact hf,
end

lemma inclusion_of_subfield_is_identity (F : set E) [is_subfield F] (x : F) : algebra_map F E x = x := by tauto

lemma algebra_map_twice : set.range (algebra_map (set.range (algebra_map F E)) E) = set.range (algebra_map F E) :=
begin
    have : is_subfield (set.range (algebra_map F E)) := range.is_subfield (algebra_map F E),
    ext, split,
    {   rintros ⟨⟨y, ⟨z, rfl⟩⟩, rfl⟩,
        exact ⟨z, rfl⟩,
    },
    {   exact λ hx, ⟨⟨x, hx⟩, rfl⟩, },
end

lemma adjoin_equals_adjoin_range (S : set E) : adjoin F S = adjoin (set.range (algebra_map F E)) S :=
by simp only [adjoin, algebra_map_twice]

lemma adjoin_simple_equals_adjoin_simple_range (α : E) : adjoin_simple F α = adjoin_simple (set.range (algebra_map F E)) α :=
adjoin_equals_adjoin_range F E {α}
