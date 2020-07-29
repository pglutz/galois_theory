import adjoin_simple
import separable
import linear_algebra.finite_dimensional

open finite_dimensional

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]


-- This should go into field_theory/subfield eventually probably
lemma is_subfield.pow_mem {K : Type*} [field K] {a : K} {n : ℤ} {s : set K} [is_subfield s] (h : a ∈ s) : a ^ n ∈ s :=
begin
    by_cases hn : n ≥ 0,
    {   lift n to ℕ using hn,
        exact is_submonoid.pow_mem h, },
    {   rw [(show n = (-1)*(-n), by ring), fpow_mul],
        lift -n to ℕ using (show -n ≥ 0, by linarith),
        rw [fpow_neg, fpow_one],
        exact is_submonoid.pow_mem (is_subfield.inv_mem h), },
end

lemma primite_element_two_inf (h_sep : is_separable F E) (α β : E) (hE : adjoin F E {α, β} = (⊤ : set E))
    (hF : infinite F) : ∃ γ, adjoin_simple F E γ = (⊤ : set E) :=
begin
    -- set f := minimal_polynomial (Exists.some $ h_sep α) with hf,
    rcases h_sep α with ⟨hα, hf⟩,
    rcases h_sep β with ⟨hβ, hg⟩,
    set f := minimal_polynomial hα,
    set g := minimal_polynomial hβ,
    sorry,
end

lemma primitive_element_fin_aux [fintype E] : ∃ α : E, adjoin_simple F E α = (⊤ : set E) :=
begin
    obtain ⟨α, hα⟩ := is_cyclic.exists_generator (units E),
    use α,
    ext,
    refine ⟨λ _, dec_trivial, λ _, _⟩,
    by_cases hx : x = 0,
    {   rw hx,
        exact is_add_submonoid.zero_mem, },
    {   obtain ⟨n, hn⟩ := set.mem_range.mp (hα (units.mk0 x hx)),
        rw (show x = (α : E)^n, by norm_cast at *; simp *),
        exact is_subfield.pow_mem (adjoin_simple_contains_element F E ↑α),
    },
end

theorem primitive_element_fin [fintype F] (hE : finite_dimensional F E) :
    ∃ α : E, adjoin_simple F E α = (⊤ : set E) :=
begin
    sorry,
end

--This might end up being changed slightly. At some point we will need to finalize this
theorem primitive_element_two (α β : E) : separable_extension F E → finite_dimensional F E → 
    (∃ γ : E, adjoin F E {α, β} = adjoin F E {γ} ) := sorry

private theorem primitive_element_aux (hs : is_separable F E) (hfd: finite_dimensional F E) :
     ∀ n : ℕ, findim F E = n → (∃ α : E, adjoin F E {α} = (⊤ : set E)) 
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
