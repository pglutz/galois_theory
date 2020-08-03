import ring_theory.algebra
import field_theory.minimal_polynomial
import field_theory.separable

/- separable extension -/

def element_is_separable (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (α : E) : Prop :=
∃ h : is_integral F α, (minimal_polynomial h).separable

lemma is_separable_iff_element_is_separable (F : Type*) [field F] {E : Type*} [field E] [algebra F E] : Prop :=
is_separable F E ↔ ∀ α : E, element_is_separable F α