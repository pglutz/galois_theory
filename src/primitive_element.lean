import adjoin
import separable
import linear_algebra.finite_dimensional
import subfield_stuff
import data.set.finite


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

lemma inf_of_subset_inf {X : Type*} {s : set X} {t : set X} (hst : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, ht.subset hst) hs

open finite_dimensional

/- Prove the primitive element theorem. -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

def roots (f : polynomial F) := {α : E | polynomial.eval₂ (algebra_map F E) α f = 0}

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

lemma primitive_element_two_aux (F : set E) [is_subfield F] (α β : E) (f g : polynomial F) (F_inf : F.infinite) :
    ∃ c : F, ∀ (β' : roots F E g) (α' : roots F E f), β ≠ β' → α + c*β ≠ α' + c*β' := sorry

/-- Primitive element theorem for adjoining two elements to an infinite field. -/
lemma primitive_element_two_inf  (F : set E) [is_subfield F] (α β : E) (F_sep : is_separable F E)
    (F_inf : F.infinite) : ∃ γ : E, adjoin F {α, β} = adjoin_simple F γ :=
begin
    rcases F_sep α with ⟨hα, hf⟩,
    rcases F_sep β with ⟨hβ, hg⟩,
    let f := minimal_polynomial hα,
    let g := minimal_polynomial hβ,
    cases primitive_element_two_aux E F α β f g F_inf with c hc,
    let γ := α + c*β,
    use γ,
    have αβ_in_Fγ : {α, β} ⊆ adjoin_simple F γ := sorry,
    have Fαβ_sub_Fγ : adjoin F {α, β} ⊆ adjoin_simple F γ :=
        adjoin_subset F {α, β} (adjoin_contains_field_set F {γ}) αβ_in_Fγ,
    have γ_in_Fαβ : ({γ} : set E) ⊆ adjoin F {α, β},
    {   intros _ h,
        cases h,
        have α_in : α ∈ (adjoin F {α, β} : set E) := adjoin_contains_element F {α, β} ⟨α, set.mem_insert α {β}⟩,
        have β_in : β ∈ (adjoin F {α, β} : set E) := adjoin_contains_element F {α, β} ⟨β, set.mem_insert_of_mem α rfl⟩,
        have cβ_in : ↑c*β ∈ (adjoin F {α, β} : set E) := is_submonoid.mul_mem (adjoin_contains_field F {α, β} c) β_in,
        exact is_add_submonoid.add_mem α_in cβ_in,
    },
    have Fγ_sub_Fαβ : adjoin_simple F γ ⊆ adjoin F {α, β} :=
        adjoin_subset F {γ} (adjoin_contains_field_set F {α, β}) γ_in_Fαβ,
    exact set.subset.antisymm Fαβ_sub_Fγ Fγ_sub_Fαβ,
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
    rw (show x = algebra_map F E ⟨x, hx⟩, from rfl),
    apply adjoin_contains_field,
end

-- Should these two lemmas go in adjoin.lean?
/- If E is a finite extension of F then it is also a finite extension of F adjoin alpha. -/
lemma adjoin_findim_of_findim (F_findim : finite_dimensional F E) (α : E) :
    finite_dimensional (adjoin_simple F α) E :=
begin
    sorry,
end

/- Adjoining an element from outside of F strictly decreases the degree of the extension if it's finite. -/
lemma adjoin_dim_lt (F : set E) [hF : is_subfield F] (F_findim : finite_dimensional F E) (α : E) (hα : α ∉ F) :
    findim (adjoin_simple F α) E < findim F E :=
begin 
    sorry,
end

/- Primitive element theorem for infinite fields when F is actually a subset of E . -/
theorem primitive_element_inf_aux (F : set E) [hF : is_subfield F] (F_sep : is_separable F E)
    (F_findim: finite_dimensional F E) (F_inf : F.infinite) (n : ℕ) (hn : findim F E = n) :
    (∃ α : E, adjoin_simple F α = (⊤ : set E)) :=
begin
    tactic.unfreeze_local_instances,
    revert F,
    apply n.strong_induction_on,
    clear n,
    intros n ih F hF F_sep F_findim F_inf hn,
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
        {   have Fα_findim : finite_dimensional (adjoin_simple F α) E := adjoin_findim_of_findim F E F_findim α,
            have Fα_le_n : findim (adjoin_simple F α) E < n :=
            begin
                rw ← hn,
                exact adjoin_dim_lt E F F_findim α hα,
            end,
            have Fα_inf : (adjoin_simple F α).infinite :=
                inf_of_subset_inf (adjoin_contains_field_as_subfield {α} F) F_inf,
            have Fα_sep : is_separable (adjoin_simple F α) E := sorry,
            obtain ⟨β, hβ⟩ := ih (findim (adjoin_simple F α) E) Fα_le_n (adjoin_simple F α)
                Fα_sep Fα_findim Fα_inf rfl,
            obtain ⟨γ, hγ⟩ := primitive_element_two_inf E F α β F_sep F_inf,
            rw [adjoin_simple_twice, hγ] at hβ,
            exact ⟨γ, hβ⟩,
        },
    },
end

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf (F_sep : is_separable F E) (F_findim : finite_dimensional F E) (F_inf : infinite F) :
    ∃ α, adjoin_simple F α = (⊤ : set E) :=
begin
    set F' := set.range (algebra_map F E) with hF',
    have F'_sep : is_separable F' E := inclusion.separable F_sep,
    have F'_findim : finite_dimensional F' E := inclusion.finite_dimensional F_findim,
    have F'_inf : F'.infinite :=
    begin
        apply set.infinite_coe_iff.mp,
        apply infinite.of_injective (set.range_factorization ⇑(algebra_map F E)),
        have : function.injective (algebra_map F E) := (algebra_map F E).injective,
        intros x y hxy,
        injections_and_clear,
        tauto,
    end,
    obtain ⟨α, hα⟩ := primitive_element_inf_aux E F' F'_sep F'_findim F'_inf (findim F' E) rfl,
    exact ⟨α, by simp only [*, adjoin_simple_equals_adjoin_simple_range]⟩,
end


/- Actual primitive element theorem. -/

/-- Primitive element theorem. -/
theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) :
    (∃ α : E, adjoin_simple F α = (⊤ : set E)) :=
begin
    by_cases F_finite : nonempty (fintype F),
    exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h hfd),
    exact primitive_element_inf F E hs hfd (not_nonempty_fintype.mp F_finite),
end

example (F : set E) [is_subfield F] (α β : E) (hα : α ∈ F) (hβ : β ∈ F) : α + β ∈ F := is_add_submonoid.add_mem hα hβ