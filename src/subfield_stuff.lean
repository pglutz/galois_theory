import field_theory.subfield
import field_theory.separable
import field_theory.tower
import data.set.finite
import algebra.gcd_domain

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

lemma reverse_inclusion_of_field (f : F) :
reverse_inclusion_ring_hom F E ↑f = f :=
begin
    change (inclusion_isomorphism F E).symm (inclusion_isomorphism F E f) = f,
    rw alg_equiv.symm_apply_apply,
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

noncomputable instance why_does_this_need_a_name : algebra (set.range (algebra_map F E)) F := {
    smul := λ e f, reverse_inclusion_ring_hom F E (e * f),
    to_fun := (reverse_inclusion_ring_hom F E),
    map_zero' := (reverse_inclusion_ring_hom F E).map_zero',
    map_add' := (reverse_inclusion_ring_hom F E).map_add',
    map_one' := (reverse_inclusion_ring_hom F E).map_one',
    map_mul' := (reverse_inclusion_ring_hom F E).map_mul',
    smul_def' :=
    begin
        intros e f,
        change reverse_inclusion_ring_hom F E (e * f) = (reverse_inclusion_ring_hom F E e) * f,
        rw ring_hom.map_mul,
        rw reverse_inclusion_of_field,
    end,
    commutes' := λ e f, mul_comm _ _,
}

instance why_does_this_also_need_a_name : is_algebra_tower (set.range (algebra_map F E)) F E := {
    smul_assoc :=
    begin
        intros x y z,
        rw algebra.smul_def'',
        change ↑(inclusion_isomorphism F E ((inclusion_isomorphism F E).symm (x * y))) * z = _,
        rw alg_equiv.apply_symm_apply,
        rw is_submonoid.coe_mul,
        rw mul_assoc,
        rw algebra.smul_def'',
        rw algebra.smul_def'',
        refl,
    end
}

noncomputable def inclusion_linear_equiv : F ≃ₗ[set.range (algebra_map F E)] set.range (algebra_map F E) := {
    to_fun := (inclusion_isomorphism F E),
    map_add' := (inclusion_isomorphism F E).map_add',
    inv_fun := (inclusion_isomorphism F E).inv_fun,
    left_inv := (inclusion_isomorphism F E).left_inv,
    right_inv := (inclusion_isomorphism F E).right_inv,
    map_smul' :=
    begin
        intros x y,
        change (inclusion_isomorphism F E ((inclusion_isomorphism F E).symm (x * y))) = x * ↑y,
        rw alg_equiv.apply_symm_apply,
    end
}

instance finite_dimensional_of_field : finite_dimensional F F :=
begin
    rw finite_dimensional.finite_dimensional_iff_dim_lt_omega,
    rw ←finite_dimensional.findim_eq_dim,
    rw finite_dimensional.findim_of_field,
    exact cardinal.nat_lt_omega 1,
end

instance wow_this_also_needs_a_name : finite_dimensional (set.range (algebra_map F E)) F :=
linear_equiv.finite_dimensional ((@inclusion_linear_equiv F _ E _ _).symm)

lemma inclusion.finite_dimensional : finite_dimensional F E → finite_dimensional (set.range (algebra_map F E)) E :=
λ h, @finite_dimensional.trans (set.range (algebra_map F E)) F E _ _ _ _ _ _ _ _ h

/-- If F is infinite then its inclusion into E is infinite. -/
lemma inclusion.infinite (hF : infinite F) : (set.range (algebra_map F E)).infinite :=
begin
    apply set.infinite_coe_iff.mp,
    apply infinite.of_injective (set.range_factorization (algebra_map F E)),
    exact subtype.coind_injective (λ (a : F), set.mem_range_self a) ((algebra_map F E).injective),
end

-- def base_field_as_submodule (F : set E) [is_subfield F] : submodule F E := {
--     carrier := F,
--     zero_mem' := is_add_submonoid.zero_mem,
--     add_mem' := λ a b, is_add_submonoid.add_mem,
--     smul_mem' :=
--     begin
--         rintros ⟨a, ha⟩ b hb,
--         exact is_submonoid.mul_mem ha hb,
--     end
-- }

-- def base_field_linear_equiv (F : set E) [is_subfield F] : F ≃ₗ[F] base_field_as_submodule F :=
-- {
--     to_fun := λ x, x,
--     map_add' := λ x y, rfl,
--     inv_fun := λ x, x,
--     left_inv := λ x, rfl,
--     right_inv := λ x, rfl,
--     map_smul' := λ x y, rfl,
-- }
