import adjoin_simple
import separable
import linear_algebra.finite_dimensional

open finite_dimensional

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*)[field E] [algebra F E]


--This might end up being changed slightly. At some point we will need to finalize this
theorem primitive_element_two (α β : E) : separable_extension F E → finite_dimensional F E → (∃ γ : E, adjoin F E {α, β} = adjoin F E {γ} ) := sorry

private theorem primitive_element_aux (hs : is_separable F E) (hfd: finite_dimensional F E) : ∀ n : ℕ, findim F E = n → (∃ α : E, adjoin F E {α} = (⊤ : set E)) 
| 0 := sorry
| 1 := 
begin
sorry
end
| (n + 2) :=
begin
sorry
end

theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) : (∃ α : E, adjoin F E {α} = (⊤ : set E)) := primitive_element_aux F E hs hfd (findim F E) rfl