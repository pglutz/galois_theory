import adjoin

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
