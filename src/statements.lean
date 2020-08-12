import field_theory.separable
import field_theory.normal
import field_theory.fixed
import group_theory.group_action
import automorphisms
import primitive_element

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

@[class] def is_galois : Prop := is_separable F E ∧ normal F E

@[class] def fin_galois : Prop := finite_dimensional F E ∧ is_galois F E

--splitting field of separable polynomial
def fin_galois' : Prop := ∃ f : polynomial F, f.separable ∧  polynomial.is_splitting_field F E f

--fixed field of aut
def fin_galois'' : Prop := finite_dimensional F E ∧ base_field_image F E = mul_action.fixed_points (E ≃ₐ[F] E) E

--fixed field of some subgroup of aut
def fin_galois''' : Prop := ∃ H : subgroup (E ≃ₐ[F] E), ∃ is_fin : fintype H,  base_field_image F E = mul_action.fixed_points H E

lemma fin_galois'_implies_fin_galois'' : fin_galois' F E → fin_galois'' F E :=
begin
    intro h,
    cases h with f hf,
    split,
    exact @polynomial.is_splitting_field.finite_dimensional F E _ _ _ f hf.2,
    sorry,
end

lemma fin_galois''_implies_fin_galois''': fin_galois'' F E → fin_galois''' F E :=
begin
    intro h,
    use (⊤ : subgroup (E ≃ₐ[F] E)),
    sorry,
end

lemma fis_galois'''_implies_fin_galois : fin_galois''' F E → fin_galois F E := sorry

lemma fin_galois_implies_fin_galois' : fin_galois F E → fin_galois' F E :=
begin
    intro h,
    cases primitive_element F h.2.1 h.1 with α hE,
    cases h.2.2 α with hα hf,
    use minimal_polynomial hα,
    sorry,
end

lemma fin_galois_iff_fin_galois' : fin_galois F E ↔ fin_galois' F E := sorry
lemma fin_galois_iff_fin_galois'' : fin_galois F E ↔ fin_galois'' F E := sorry
lemma fin_galois_iff_fin_galois''' : fin_galois F E ↔ fin_galois''' F E := sorry
