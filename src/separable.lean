import ring_theory.algebra
import field_theory.minimal_polynomial
import field_theory.separable

/- separable extension -/

definition separable_element (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (α : E) : Prop :=
∃ (h : is_integral F α), (polynomial.separable (minimal_polynomial h))

--actually, a new version of mathlib might have "is_separable F E" in field_theory.separable
definition separable_extension (F : Type*) [field F] (E : Type*) [field E] [algebra F E] : Prop :=
∀ α : E, separable_element F α
