import ring_theory.algebra
import field_theory.minimal_polynomial
import field_theory.separable

/- separable extension -/

definition separable_element (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (α : E) : Prop :=
∃ (h : is_integral F α), (minimal_polynomial h).separable

definition separable_extension (F : Type*) [field F] (E : Type*) [field E] [algebra F E] : Prop :=
∀ α : E, separable_element F α

--actually, a new version of mathlib might have this definition of is_separable. It seems like it doesn't
@[class] def is_separable (F K : Sort*) [field F] [field K] [algebra F K] : Prop :=
∀ x : K, ∃ H : is_integral F x, (minimal_polynomial H).separable