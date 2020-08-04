import field_theory.separable
import field_theory.normal

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

definition is_galois : Prop := finite_dimensional F E ∧ is_separable F E ∧ normal F E

instance aut : group (E ≃ₐ[F] E) := {
    mul := alg_equiv.trans,
    mul_assoc := λ ϕ ψ χ, rfl,
    one := 1,
    one_mul := λ ϕ, by {ext,refl},
    mul_one := λ ϕ, by {ext,refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext,exact alg_equiv.apply_symm_apply ϕ a},
}