import adjoin
import separable
import linear_algebra.finite_dimensional

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

--This might end up being changed slightly. At some point we will need to finalize this
theorem primitive_element : (is_separable F E ∧ finite_dimensional F E) → (∃ α : E, adjoin F E α = (⊤ : set E)) := sorry
