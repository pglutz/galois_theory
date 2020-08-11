import primitive_element

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

instance aut_action : mul_action (E ≃ₐ[F] E) E := {
    smul := alg_equiv.to_fun,
    one_smul := λ x, rfl,
    mul_smul := λ ϕ ψ x, rfl,
}

instance aut_subgroup_action (H : subgroup (E ≃ₐ[F] E)) : mul_action H E :=
mul_action.comp_hom E (subgroup.subtype H)

definition base_field_image := set.range (algebra_map F E)

lemma base_field_is_fixed : base_field_image F E ⊆ mul_action.fixed_points (E ≃ₐ[F] E) E :=
begin
    intros x hx ϕ,
    cases hx with f hf,
    rw ←hf,
    exact alg_equiv.commutes ϕ f,
end

--things to do:
--  give notation for aut
--  define fixed field and show that it is indeed a field
--  maybe use group actions more generally rather than just subgroups of (E ≃ₐ[F] E)
--  prove Artin's theorem that [E : E^G] ≤ |G|
--  show that if extension is finite separable then cardinality of automorphism group ≤ [E : F]
--  show that if G is finite then G = Aut(E / E^G)
