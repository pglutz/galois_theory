import adjoin
import separable

/- Prove the primitive element theorem. -/



variables (F : Type*) [field F] (K : Type*) [field K] [algebra F K]

theorem primitive_element : separable F K → (∃ α : K, adjoin F K α = (⊤ : set K)) := sorry