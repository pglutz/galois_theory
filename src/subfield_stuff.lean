import ring_theory.algebra
import field_theory.subfield
import field_theory.separable

section

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

definition inclusion_ring_hom : F →+* (set.range (algebra_map F E)) := {
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
}

lemma algebra_map_comp : (algebra_map (set.range (algebra_map F E)) E).comp(inclusion_ring_hom F E) = algebra_map F E :=
begin
    ext,
    refl,
end

instance : algebra F (set.range (algebra_map F E)) := {
    smul := λ f e, f * e,
    to_fun := inclusion_ring_hom F E,
    map_zero' := (inclusion_ring_hom F E).map_zero',
    map_add' := (inclusion_ring_hom F E).map_add',
    map_one' := (inclusion_ring_hom F E).map_one',
    map_mul' := (inclusion_ring_hom F E).map_mul',
    smul_def' := λ f e, rfl,
    commutes' :=
    begin
        intros f e,
        ext1, unfold_coes, simp[mul_comm],
    end,
}

definition inclusion_algebra_hom : F →ₐ[F] set.range (algebra_map F E) := {
    to_fun := λ f, f,
    map_zero' := (inclusion_ring_hom F E).map_zero',
    map_add' := (inclusion_ring_hom F E).map_add',
    map_one' := (inclusion_ring_hom F E).map_one',
    map_mul' := (inclusion_ring_hom F E).map_mul',
    commutes' := λ f, rfl,
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

noncomputable def reverse_inclusion_ring_hom : set.range (algebra_map F E) →+* F :=
(inclusion_isomorphism F E).symm

lemma reverse_inclusion_comp :
(algebra_map F E).comp(reverse_inclusion_ring_hom F E) = algebra_map _ E :=
begin
    ext,
    cases x with x hx,
    cases hx with f hf,
    have swap : (⟨x,⟨f,hf⟩⟩ : set.range(algebra_map F E)) = inclusion_ring_hom F E f,
    ext,
    exact hf.symm,
    rw swap,
    change algebra_map F E ((inclusion_isomorphism F E).symm (inclusion_isomorphism F E f)) = _,
    rw alg_equiv.symm_apply_apply,
    refl,
end

end

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {x : E}

lemma inclusion.integral (hx : is_integral F x) : is_integral (set.range (algebra_map F E)) x :=
begin
    set F' := set.range (algebra_map F E),
    set f := inclusion_ring_hom F E,
    cases hx with p hp,
    use p.map f,
    split,
    apply polynomial.monic_map,
    exact hp.1,
    dsimp[polynomial.aeval],
    rw polynomial.eval₂_map,
    rw algebra_map_comp,
    exact hp.2,
end

lemma inclusion.minimal_polynomial (hx : is_integral F x) : minimal_polynomial (inclusion.integral hx) = (minimal_polynomial hx).map (inclusion_ring_hom F E) :=
begin
    set F' := set.range (algebra_map F E),
    set f := inclusion_ring_hom F E,
    symmetry,
    apply minimal_polynomial.unique,
    apply polynomial.monic_map,
    apply minimal_polynomial.monic,
    dsimp[polynomial.aeval],
    rw polynomial.eval₂_map,
    rw algebra_map_comp,
    apply minimal_polynomial.aeval,
    intros q hq1 hq2,
    set f' := reverse_inclusion_ring_hom F E,
    set p := q.map f',
    rw polynomial.degree_map_eq_of_leading_coeff_ne_zero,
    apply ge_trans (polynomial.degree_map_le f'),
    apply minimal_polynomial.degree_le_of_ne_zero,
    exact polynomial.map_monic_ne_zero hq1,
    dsimp[polynomial.aeval],
    rw polynomial.eval₂_map,
    rw reverse_inclusion_comp,
    exact hq2,
    rw ring_hom.map_ne_zero,
    intro h,
    rw polynomial.leading_coeff_eq_zero at h,
    exact minimal_polynomial.ne_zero hx h,
end

lemma inclusion.separable : is_separable F E → is_separable (set.range (algebra_map F E)) E :=
begin
    intros h x,
    cases h x with hx hs,
    use inclusion.integral hx,
    rw inclusion.minimal_polynomial,
    exact polynomial.separable.map hs,
end