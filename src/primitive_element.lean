import adjoin
import separable

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

theorem primitive_element : separable F E → (∃ α : E, adjoin F E α = (⊤ : set E)) := sorry
