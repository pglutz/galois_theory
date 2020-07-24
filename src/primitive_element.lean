import adjoin
import separable
import linear_algebra

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

theorem primitive_element : separable_extension F E → finite_dimensional F E → (∃ α : E, adjoin F E α = (⊤ : set E)) := sorry
