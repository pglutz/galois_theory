import ring_theory.algebra
import field_theory.minimal_polynomial
import field_theory.separable
import adjoin

/- Separable extension -/

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

def element_is_separable (α : E) : Prop := ∃ h : is_integral F α, (minimal_polynomial h).separable

lemma is_separable_iff_element_is_separable : is_separable F E ↔ ∀ α : E, element_is_separable F α := sorry

lemma adjoin_simple_is_separable (F_sep : is_separable F E) (α : E) : is_separable (adjoin_simple F α) E :=
begin
    intro x,
    obtain ⟨x_int_F, hx⟩ := F_sep x,
    have x_int_Fα : is_integral (adjoin_simple F α) x := sorry,
    use x_int_Fα,
    sorry,
end