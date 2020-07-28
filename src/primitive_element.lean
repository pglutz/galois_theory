import adjoin_simple
import separable
import linear_algebra.finite_dimensional

/- Prove the primitive element theorem. -/

variables (E : Type*) [field E] (F : Type*) [field F] [algebra F E]

--This might end up being changed slightly. At some point we will need to finalize this
theorem primitive_element : (is_separable F E ∧ finite_dimensional F E) → (∃ α : E, adjoin_simple F E α = (⊤ : set E)) := sorry
