import field_theory.separable
import field_theory.normal
import field_theory.fixed
import group_theory.group_action

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

@[class] def is_galois : Prop := is_separable F E ∧ normal F E

@[class] def fin_galois : Prop := finite_dimensional F E ∧ is_galois F E

instance aut : group (E ≃ₐ[F] E) := {
    mul := λ ϕ ψ, ψ.trans ϕ,
    mul_assoc := λ ϕ ψ χ, rfl,
    one := 1,
    one_mul := λ ϕ, by {ext,refl},
    mul_one := λ ϕ, by {ext,refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext,exact alg_equiv.symm_apply_apply ϕ a},
}

instance wahooo_lean_wants_a_name_for_this : mul_action (E ≃ₐ[F] E) E := {
    smul := alg_equiv.to_fun,
    one_smul := λ x, rfl,
    mul_smul := λ ϕ ψ x, rfl,
}

instance wahooo_lean_wants_a_name_for_this' (H : subgroup (E ≃ₐ[F] E)) : mul_action H E :=
mul_action.comp_hom E (subgroup.subtype H)

definition base_field_image := set.range (algebra_map F E)

lemma base_field_is_fixed : base_field_image F E ⊆ mul_action.fixed_points (E ≃ₐ[F] E) E :=
begin
    intros x hx ϕ,
    cases hx with f hf,
    rw ←hf,
    exact alg_equiv.commutes ϕ f,
end

--splitting field of separable polynomial
definition is_galois' : Prop := sorry

--fixed field of aut
definition is_galois'' : Prop := base_field_image F E = mul_action.fixed_points (E ≃ₐ[F] E) E

--fixed field of some subgroup of aut
definition is_galois''' : Prop := ∃ H : subgroup (E ≃ₐ[F] E), base_field_image F E = mul_action.fixed_points H E