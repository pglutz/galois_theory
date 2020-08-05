import adjoin
import separable
import linear_algebra.finite_dimensional


-- This should go into field_theory/subfield eventually probably
lemma is_subfield.pow_mem {K : Type*} [field K] {a : K} {n : ℤ} {s : set K} [is_subfield s] (h : a ∈ s) : a ^ n ∈ s :=
begin
    by_cases hn : n ≥ 0,
    {   lift n to ℕ using hn,
        exact is_submonoid.pow_mem h, },
    {   rw [(show n = (-1)*(-n), by ring), fpow_mul, fpow_neg a, fpow_one],
        lift -n to ℕ using (show -n ≥ 0, by linarith),
        exact is_submonoid.pow_mem (is_subfield.inv_mem h), },
end

open finite_dimensional

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/- Primitive element theorem for finite fields. -/

-- Replaces earlier messy proof, courtesy of Aaron Anderson & Markus Himmel on zulip
noncomputable def finite_of_findim_over_finite [fintype F] (hE : finite_dimensional F E) : fintype E :=
    module.fintype_of_fintype (classical.some_spec (finite_dimensional.exists_is_basis_finset F E) : _)

/-- Primitive element theorem for F ⊂ E assuming E is finite. -/
lemma primitive_element_fin_aux [fintype E] : ∃ α : E, adjoin_simple F α = (⊤ : set E) :=
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
        exact is_subfield.pow_mem (adjoin_simple_contains_element F ↑α),
    },
end

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem primitive_element_fin [fintype F] (hfd : finite_dimensional F E) :
    ∃ α : E, adjoin_simple F α = (⊤ : set E) := @primitive_element_fin_aux F _ E _ _ (finite_of_findim_over_finite F E hfd)

/- Primitive element theorem for infinite fields. -/

--Milne's version
lemma primitive_element_two_inf_milne (α β : E) (hα : element_is_separable F α) (hF : infinite F) :
    ∃ γ : E, adjoin F {α, β} = adjoin_simple F γ := sorry

/-- Primitive element theorem for adjoining two elements to an infinite field. -/
lemma primitive_element_two_inf  (α β : E) (h_sep : is_separable F E) (hF : infinite F) :
    ∃ γ : E, adjoin F {α, β} = adjoin_simple F γ :=
begin
    -- set f := minimal_polynomial (Exists.some $ h_sep α) with hf,
    rcases h_sep α with ⟨hα, hf⟩,
    rcases h_sep β with ⟨hβ, hg⟩,
    set f := minimal_polynomial hα,
    set g := minimal_polynomial hβ,
    sorry,
end

/- Primitive element theorem when F = E. -/
lemma primitive_element_trivial (F : set E) (hF : is_subfield F) (F_eq_E : F = (⊤ : set E)) :
    ∃ α : E, adjoin_simple F α = (⊤ : set E) :=
begin
    use 0,
    ext,
    split,
    intro _,
    exact dec_trivial,
    rw ← F_eq_E,
    intro hx,
    have : x = algebra_map F E ⟨x, hx⟩ := rfl,
    rw this,
    apply adjoin_contains_field,
end

/- Primitive element theorem for adjoining two elements when F is actually a subset of E rather than just having an 
    embedding into E. -/
theorem primitive_element_inf_aux' (F : set E) (hF : is_subfield F) (h_sep : is_separable F E) (h_dim: finite_dimensional F E) (h_inf : infinite F)
     (n : ℕ) (hn : findim F E = n) : (∃ α : E, adjoin_simple F α = (⊤ : set E)) :=
begin
    tactic.unfreeze_local_instances,
    revert F,
    apply n.strong_induction_on,
    clear n,
    intros n ih F hF h_sep h_finddim h_inf hn,
    by_cases F_neq_E : F = (⊤ : set E),
    {   exact primitive_element_trivial E F hF F_neq_E, },
    {   have : ∃ α : E, α ∉ F :=
        begin
            revert F_neq_E,
            contrapose!,
            exact λ h, set.ext (λ x, ⟨λ _, dec_trivial, λ _, h x⟩),
        end,
        rcases this with ⟨α, hα⟩,
        by_cases h : adjoin_simple F α = (⊤ : set E),
        {   exact ⟨α, h⟩,   },
        {   have Fα_findim : finite_dimensional (adjoin_simple F α) E := sorry,
            have Fα_le_n : findim (adjoin_simple F α) E < n := sorry,
            have Fα_inf : infinite (adjoin_simple F α) := sorry,
            have Fα_sep : is_separable (adjoin_simple F α) E := sorry,
            obtain ⟨β, hβ⟩ := ih (findim (adjoin_simple F α) E) Fα_le_n (adjoin_simple F α) _
                Fα_sep Fα_findim Fα_inf rfl,
            obtain ⟨γ, hγ⟩ := primitive_element_two_inf F E α β h_sep h_inf,
            rw [adjoin_simple_twice, hγ] at hβ,
            exact ⟨γ, hβ⟩,
        },
    },
end

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf_aux (h_sep : is_separable F E) (h_dim: finite_dimensional F E) (h_inf : infinite F)
     (n : ℕ) (hn : findim F E = n) : (∃ α : E, adjoin_simple F α = (⊤ : set E)) :=
begin
    sorry,
end

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf (hs : is_separable F E) (hfd : finite_dimensional F E) (hF : infinite F) :
    ∃ α, adjoin_simple F α = (⊤ : set E) := primitive_element_inf_aux F E hs hfd hF (findim F E) rfl

/-- Primitive element theorem. -/
theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) :
    (∃ α : E, adjoin_simple F α = (⊤ : set E)) :=
begin
    by_cases F_finite : nonempty (fintype F),
    exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h hfd),
    exact primitive_element_inf F E hs hfd (not_nonempty_fintype.mp F_finite),
end
