import primitive_element
import field_theory.fixed

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

instance aut : group (E ≃ₐ[F] E) := {
    mul := λ ϕ ψ, ψ.trans ϕ,
    mul_assoc := λ ϕ ψ χ, rfl,
    one := 1,
    one_mul := λ ϕ, by {ext,refl},
    mul_one := λ ϕ, by {ext,refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext,exact alg_equiv.symm_apply_apply ϕ a},
}

instance aut_action : mul_semiring_action (E ≃ₐ[F] E) E := {
    smul := alg_equiv.to_fun,
    smul_zero := alg_equiv.map_zero,
    smul_one := alg_equiv.map_one,
    one_smul := λ _, rfl,
    smul_add := alg_equiv.map_add,
    smul_mul := alg_equiv.map_mul,
    mul_smul := λ _ _ _, rfl,
}

instance subgroup_action (G : Type*) [group G] [mul_semiring_action G E] (H : subgroup G) :
mul_semiring_action H E := {
    smul := λ h e, (↑h : G) • e,
    smul_zero := λ _, smul_zero _,
    smul_one := λ _, smul_one _,
    one_smul := one_smul G,
    smul_add := λ _, smul_add _,
    smul_mul := λ _, mul_semiring_action.smul_mul _,
    mul_smul := λ x y _, mul_action.mul_smul ↑x ↑y _,
}

lemma base_field_is_fixed : set.range (algebra_map F E) ⊆ mul_action.fixed_points (E ≃ₐ[F] E) E :=
begin
    intros x hx ϕ,
    cases hx with f hf,
    rw ←hf,
    exact alg_equiv.commutes ϕ f,
end

theorem artin_inequality (G : Type*) [group G] [fintype G] [mul_semiring_action G E] :
vector_space.dim (mul_action.fixed_points G E) E ≤ fintype.card G :=
begin
    set F := mul_action.fixed_points G E,
    cases exists_is_basis F E with b hb,
    rw ← is_basis.mk_range_eq_dim hb,
    apply le_trans cardinal.mk_range_le,
    replace hb := hb.left,
end

--things to do:
--  give notation for aut
--  define fixed field and show that it is indeed a field
--  maybe use group actions more generally rather than just subgroups of (E ≃ₐ[F] E)
--  prove Artin's theorem that [E : E^G] ≤ |G|
--  show that if extension is finite separable then cardinality of automorphism group ≤ [E : F]
--  show that if G is finite then G = Aut(E / E^G)
