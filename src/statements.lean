import field_theory.separable
import field_theory.normal

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

definition is_galois : Prop := is_separable F E ∧ normal F E