import adjoin
import separable
import linear_algebra.finite_dimensional
import subfield_stuff
import data.set.finite
import field_theory.tower


/- Some stupid lemmas used below. Maybe some of them are already in mathlib? -/

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

/-- If a subset of a set is infinite then the set is infinite. -/
lemma inf_of_subset_inf {X : Type*} {s : set X} {t : set X} (hst : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, ht.subset hst) hs

-- Is this really not in mathlib
/-- If M is an algebra over a field F and x is a nonzero element of F then x as an element of M is also nonzero. -/
lemma ne_zero_of_ne_zero (F M : Type*) [field F] [comm_semiring M] [nontrivial M] [algebra F M]
    {x : F} (hx : x ≠ 0) : algebra_map F M x ≠ 0 :=
begin
    revert hx,
    contrapose!,
    intro h,
    rw ← (algebra_map F M).map_zero at h,
    exact (algebra_map F M).injective h,
end


/- Proof of the primitive element theorem. -/

open finite_dimensional

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- The set of roots of a polynomial f in a field E where f is a polynomial in F and F ⊆ E. -/
def roots (f : polynomial F) := {α : E | polynomial.eval₂ (algebra_map F E) α f = 0}

/- Trivial case of the primitive element theorem. -/

/-- Primitive element theorem when F = E. -/
lemma primitive_element_trivial (F : set E) (hF : is_subfield F) (F_eq_E : F = (⊤ : set E)) :
    ∃ α : E, F[α] = (⊤ : set E) :=
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

/- Primitive element theorem for finite fields. -/

-- Replaces earlier messy proof, courtesy of Aaron Anderson & Markus Himmel on zulip
/-- A finite dimensional vector space over a finite field is finite. -/
noncomputable def finite_of_findim_over_finite [fintype F] (hE : finite_dimensional F E) : fintype E :=
    module.fintype_of_fintype (classical.some_spec (finite_dimensional.exists_is_basis_finset F E) : _)

/-- Primitive element theorem for F ⊂ E assuming E is finite. -/
lemma primitive_element_fin_aux [fintype E] : ∃ α : E, F[α] = (⊤ : set E) :=
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
    ∃ α : E, F[α] = (⊤ : set E) := @primitive_element_fin_aux F _ E _ _ (finite_of_findim_over_finite F E hfd)

/- Primitive element theorem for infinite fields. -/

lemma primitive_element_two_aux (F : set E) [is_subfield F] (α β : E) (f g : polynomial F) (F_inf : F.infinite) :
    ∃ c : F, c ≠ 0 ∧ ∀ (β' : roots F E g) (α' : roots F E f), β ≠ β' → α + c*β ≠ α' + c*β' := sorry

/-- Primitive element theorem for adjoining two elements to an infinite field. -/
lemma primitive_element_two_inf  (F : set E) [is_subfield F] (α β : E) (F_sep : is_separable F E)
    (F_inf : F.infinite) : ∃ γ : E, F[α, β] = F[γ] :=
begin
    rcases F_sep α with ⟨hα, hf⟩,
    rcases F_sep β with ⟨hβ, hg⟩,
    let f := minimal_polynomial hα,
    let g := minimal_polynomial hβ,
    rcases primitive_element_two_aux E F α β f g F_inf with ⟨c, c_ne_0, hc⟩,
    replace c_ne_0 : (c : E) ≠ 0 := ne_zero_of_ne_zero F E c_ne_0,
    let γ := α + c*β,
    have α_in_Fγ : α ∈ F[γ] := sorry,
    have γ_in_Fγ : γ ∈ F[γ] := adjoin_simple_contains_element F γ,
    have c_in_Fγ : ↑c ∈ F[γ] := adjoin_simple_contains_field F γ c,
    have c_inv_in_Fγ : ↑c⁻¹ ∈ F[γ] := is_subfield.inv_mem c_in_Fγ,
    have cβ_in_Fγ : ↑c*β ∈ F[γ] := by rw (show ↑c*β = γ - α, by simp *);
        exact is_add_subgroup.sub_mem (F[γ]) γ α γ_in_Fγ α_in_Fγ,
    have β_in_Fγ : β ∈ F[γ] := by rw (show β = c⁻¹*(c*β), by simp *);
        exact is_submonoid.mul_mem c_inv_in_Fγ cβ_in_Fγ,
    have αβ_in_Fγ : {α, β} ⊆ F[γ] := λ x hx, by cases hx; cases hx; assumption,
    have Fαβ_sub_Fγ : F[α, β] ⊆ F[γ] := adjoin_subset' F {α, β} αβ_in_Fγ,
    have α_in_Fαβ : α ∈ F[α, β] := adjoin_contains_element F {α, β} ⟨α, set.mem_insert α {β}⟩,
    have β_in_Fαβ : β ∈ F[α, β] := adjoin_contains_element F {α, β} ⟨β, set.mem_insert_of_mem α rfl⟩,
    have c_in_Fαβ : ↑c ∈ (F[α, β] : set E) := adjoin_contains_field F {α, β} c,
    have cβ_in_Fαβ : ↑c*β ∈ F[α, β] := is_submonoid.mul_mem c_in_Fαβ β_in_Fαβ,
    have γ_in_Fαβ : γ ∈ F[α, β] := is_add_submonoid.add_mem α_in_Fαβ cβ_in_Fαβ,
    have Fγ_sub_Fαβ : F[γ] ⊆ F[α, β] := adjoin_simple_subset' F γ γ_in_Fαβ,
    exact ⟨γ, set.subset.antisymm Fαβ_sub_Fγ Fγ_sub_Fαβ⟩,
end

def submodule_restrict_field (α : E) (p : submodule (F[α]) E) : submodule F E := {
    carrier := p.carrier,
    zero_mem' := p.zero_mem',
    add_mem' := p.add_mem',
    smul_mem' :=
    begin
        intros c x hx,
        rw algebra.smul_def,
        rw adjoin_simple.composition F α,
        rw ring_hom.comp_apply,
        rw ←algebra.smul_def,
        exact p.smul_mem' _ hx,
    end
}

-- Should these two lemmas go in adjoin.lean?
/-- If E is a finite extension of F then it is also a finite extension of F adjoin alpha. -/
instance adjoin_findim_of_findim [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional (F[α]) E :=
begin
    rw iff_fg,
    rw submodule.fg_iff_finite_dimensional,
    cases (finite_dimensional.exists_is_basis_finite F E) with B hB,
    have key : submodule.span (F[α]) B = ⊤,
    ext,
    simp only [submodule.mem_top, iff_true],
    have hx : x ∈ submodule.span F (set.range coe),
    rw hB.1.2,
    exact submodule.mem_top,
    rw submodule.mem_span,
    intros p hp,
    rw submodule.mem_span at hx,
    apply hx (submodule_restrict_field F E α p),
    rw subtype.range_coe,
    exact hp,
    rw ←key,
    apply finite_dimensional.span_of_finite (F[α]) hB.2,
end

instance adjoin_simple_is_findim (α : E) : finite_dimensional F (F[α]) := sorry

/-- Adjoining an element from outside of F strictly decreases the degree of the extension if it's finite. -/
lemma adjoin_dim_lt (F : set E) [hF : is_subfield F] [F_findim : finite_dimensional F E] (α : E) (hα : α ∉ F) :
    findim (F[α]) E < findim F E :=
begin 
    rw ← findim_mul_findim F (F[α]) E,
    have : findim (F[α]) E > 0 := sorry,
    have : findim F (F[α]) > 1 := sorry,
    have : findim (F[α]) E > 0 := sorry,
    nlinarith,
end

/-- Primitive element theorem for infinite fields when F is actually a subset of E . -/
theorem primitive_element_inf_aux (F : set E) [hF : is_subfield F] (F_sep : is_separable F E)
    (F_findim: finite_dimensional F E) (F_inf : F.infinite) (n : ℕ) (hn : findim F E = n) :
    (∃ α : E, F[α] = (⊤ : set E)) :=
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
        by_cases h : F[α] = (⊤ : set E),
        {   exact ⟨α, h⟩,   },
        {   have Fα_findim : finite_dimensional (F[α]) E := adjoin_findim_of_findim F E α,
            have Fα_le_n : findim (F[α]) E < n := by rw ← hn; exact adjoin_dim_lt E F α hα,
            have Fα_inf : (F[α]).infinite :=
                inf_of_subset_inf (adjoin_contains_field_as_subfield {α} F) F_inf,
            have Fα_sep : is_separable (F[α]) E := adjoin_simple_is_separable F F_sep α,
            obtain ⟨β, hβ⟩ := ih (findim (F[α]) E) Fα_le_n (F[α])
                Fα_sep Fα_findim Fα_inf rfl,
            obtain ⟨γ, hγ⟩ := primitive_element_two_inf E F α β F_sep F_inf,
            rw [adjoin_simple_twice, hγ] at hβ,
            exact ⟨γ, hβ⟩,
        },
    },
end

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf (F_sep : is_separable F E) (F_findim : finite_dimensional F E) (F_inf : infinite F) :
    ∃ α, F[α] = (⊤ : set E) :=
begin
    set F' := set.range (algebra_map F E) with hF',
    have F'_sep : is_separable F' E := inclusion.separable F_sep,
    have F'_findim : finite_dimensional F' E := inclusion.finite_dimensional F_findim,
    have F'_inf : F'.infinite := inclusion.infinite F_inf,
    obtain ⟨α, hα⟩ := primitive_element_inf_aux E F' F'_sep F'_findim F'_inf (findim F' E) rfl,
    exact ⟨α, by simp only [*, adjoin_simple_equals_adjoin_simple_range]⟩,
end


/- Actual primitive element theorem. -/

/-- Primitive element theorem. -/
theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) :
    (∃ α : E, F[α] = (⊤ : set E)) :=
begin
    by_cases F_finite : nonempty (fintype F),
    exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h hfd),
    exact primitive_element_inf F E hs hfd (not_nonempty_fintype.mp F_finite),
end
