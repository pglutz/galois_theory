import field_theory.separable
import field_theory.normal
import group_theory.group_action

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

@[class] def is_galois : Prop := is_separable F E ∧ normal F E

@[class] def fin_galois : Prop := finite_dimensional F E ∧ is_galois F E

instance aut : group (E ≃ₐ[F] E ) := {
    mul := alg_equiv.trans,
    mul_assoc := λ ϕ ψ χ, rfl,
    one := 1,
    one_mul := λ ϕ, by {ext,refl},
    mul_one := λ ϕ, by {ext,refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext,exact alg_equiv.apply_symm_apply ϕ a},
}

instance tada' : has_scalar (E ≃ₐ[F] E) E := {
    smul := sorry
}

instance tada : mul_action (E ≃ₐ[F] E) E := {
    
}

--splitting field of separable polynomial
definition is_galois' : Prop := sorry

--fixed field of aut
definition is_galois'' : Prop := sorry

--fixed field of some subgroup of aut
definition is_galois''' : Prop := sorry