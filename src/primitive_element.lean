import adjoin
import linear_algebra.finite_dimensional
import linear_algebra.basic
import data.set.finite
import field_theory.tower
import algebra.gcd_monoid
import field_theory.splitting_field
import field_theory.separable

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

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

-- Is this really not in mathlib?
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

namespace polynomial

variables (F : Type*) [field F]

lemma gcd_eval_zero (f g : polynomial F) (α : F) (hf : f.eval α = 0) (hg : g.eval α = 0) : (euclidean_domain.gcd f g).eval α = 0 :=
begin
    rw euclidean_domain.gcd_eq_gcd_ab f g,
    rw [polynomial.eval_add,polynomial.eval_mul,polynomial.eval_mul,hf,hg,zero_mul,zero_mul,zero_add],
end

variables {E : Type*} [field E] [algebra F E]

lemma gcd_root_left (f g : polynomial F) (α : E) (hα : (euclidean_domain.gcd f g).eval₂ (algebra_map F E) α = 0) :
f.eval₂ (algebra_map F E) α = 0 :=
begin
    cases euclidean_domain.gcd_dvd_left f g with p hp,
    rw [hp,polynomial.eval₂_mul,hα,zero_mul],
end

lemma gcd_root_right (f g : polynomial F) (α : E) (hα : (euclidean_domain.gcd f g).eval₂ (algebra_map F E) α = 0) :
g.eval₂ (algebra_map F E) α = 0 :=
begin
    cases euclidean_domain.gcd_dvd_right f g with p hp,
    rw [hp,polynomial.eval₂_mul,hα,zero_mul],
end

end polynomial


/- Proof of the primitive element theorem. -/

open finite_dimensional

/- Trivial case of the primitive element theorem. -/

section
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

/-- Primitive element theorem when F = E. -/
lemma primitive_element_trivial (F_eq_E : base_field_image F E = (⊤ : set E)) :
    ∃ α : E, F[α] = (⊤ : set E) :=
begin
    use 0,
    ext,
    split,
    exact λ _, trivial,
    rw ← F_eq_E,
    rintros ⟨x, rfl⟩,
    apply adjoin.field_mem,
end


end

/- Primitive element theorem for finite fields. -/

section
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

-- Replaces earlier messy proof, courtesy of Aaron Anderson & Markus Himmel on zulip
/-- A finite dimensional vector space over a finite field is finite. -/
def finite_of_findim_over_finite [fintype F] [hE : finite_dimensional F E] : fintype E :=
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
theorem primitive_element_fin [fintype F] [hfd : finite_dimensional F E] :
    ∃ α : E, F[α] = (⊤ : set E) := 
begin
    haveI : fintype E := finite_of_findim_over_finite F,
    exact primitive_element_fin_aux F,
end 

end

/- Primitive element theorem for infinite fields. -/

section
variables {F : Type*} [field F] {E : Type*} [field E] (ϕ : F →+* E)

lemma primitive_element_two_aux (ϕ : F →+* E) (α β : E) {f g : polynomial F} [F_inf : infinite F] (hf : f ≠ 0) (hg : g ≠ 0) (f_monic : polynomial.monic f) (g_monic : polynomial.monic g) :
    ∃ c : F, ∀ (α' ∈ (f.map ϕ).roots) (β' ∈ (g.map ϕ).roots), β' ≠ β → ϕ c ≠ -(α' - α)/(β' - β) :=
begin
    let sf := (f.map ϕ).roots,
    let sg := (g.map ϕ).roots,
    let s := {c : E | ∃ (α' ∈ sf) (β' ∈ sg), β' ≠ β ∧ c = -(α' - α)/(β' - β)},
    let s' := ϕ⁻¹' s,
    let r : E → E → E := λ α' β', -(α' - α)/(β' - β),
    have hr : ∀ c ∈ s, ∃ α' β', ((α' ∈ sf) ∧ (β' ∈ sg)) ∧ r α' β' = c :=
    begin
        intros c hc,
        rw set.mem_set_of_eq at hc,
        tauto,
    end,
    have s_fin : s.finite :=
    begin
        refine (set.finite.image (λ z : E × E, r z.1 z.2) (set.finite_mem_finset (sf.product sg))).subset _,
        simpa only [set.subset_def, set.mem_image, prod.exists, finset.mem_product] using hr,
    end,
    have s'_fin : s'.finite := s_fin.preimage ((ring_hom.injective ϕ).inj_on (⇑ϕ ⁻¹' s)),
    obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s'_fin.to_finset,
    rw [set.finite.mem_to_finset, set.mem_preimage, set.mem_set_of_eq] at hc,
    push_neg at hc,
    exact ⟨c, hc⟩,
end

lemma primitive_element_two_inf_key_aux {β : F} {h : polynomial F} (h_ne_zero : h ≠ 0) (h_sep : h.separable)
(h_root : h.eval β = 0) (h_splits : polynomial.splits ϕ h) (h_roots : ∀ x ∈ (h.map ϕ).roots, x = ϕ β) :
h = (polynomial.C (polynomial.leading_coeff h)) * (polynomial.X - polynomial.C β) :=
begin
    have h_map_separable : (h.map ϕ).separable :=
    begin
        apply polynomial.separable.map,
        exact h_sep,
    end,
    rw polynomial.splits_iff_exists_multiset at h_splits,
    cases h_splits with s hs,
    have s_elements : ∀ x ∈ s, x = ϕ β :=
    begin
        intros x hx,
        have is_root : x ∈ (h.map ϕ).roots,
        rw polynomial.mem_roots,
        dsimp[polynomial.is_root],
        rw polynomial.eval_map,
        rw polynomial.eval₂_eq_eval_map,
        rw hs,
        rw polynomial.eval_mul,
        cases multiset.exists_cons_of_mem hx with y hy,
        rw hy,
        rw multiset.map_cons,
        simp only [polynomial.eval_X, multiset.prod_cons, polynomial.eval_C, zero_mul, polynomial.eval_mul, polynomial.eval_sub, mul_zero, sub_self],
        exact polynomial.map_ne_zero h_ne_zero,
        exact h_roots x is_root,
    end,
    replace s_elements : ∀ x ∈ multiset.map (λ (a : E), polynomial.X - polynomial.C a) s, x = polynomial.X - polynomial.C (ϕ β) :=
    begin
        intros x hx,
        rw multiset.mem_map at hx,
        cases hx with a ha,
        specialize s_elements a ha.1,
        rw s_elements at ha,
        exact ha.2.symm,
    end,
    replace s_elements := multiset.eq_repeat_of_mem s_elements,
    rw s_elements at hs,
    rw multiset.prod_repeat at hs,
    rw multiset.card_map at hs,
    rw hs at h_map_separable,
    have hf : ¬is_unit (polynomial.X - polynomial.C (ϕ β)) :=
    begin
        rw polynomial.is_unit_iff_degree_eq_zero,
        rw polynomial.degree_X_sub_C,
        exact dec_trivial,
    end,
    have map_injective := polynomial.map_injective ϕ ϕ.injective,
    have hn : s.card ≠ 0 :=
    begin
        intro hs_card,
        rw hs_card at hs,
        rw pow_zero at hs,
        rw mul_one at hs,
        rw ←polynomial.map_C at hs,
        replace hs := map_injective hs,
        rw hs at h_root,
        rw polynomial.eval_C at h_root,
        rw polynomial.leading_coeff_eq_zero at h_root,
        exact h_ne_zero h_root,
    end,
    rw (polynomial.separable.of_pow hf hn (polynomial.separable.of_mul_right h_map_separable)).2 at hs,
    rw pow_one at hs,
    apply map_injective,
    rw hs,
    rw polynomial.map_mul,
    rw polynomial.map_C,
    rw polynomial.map_sub,
    rw polynomial.map_X,
    rw polynomial.map_C,
end

end

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma primitive_element_two_inf_key (α β : E) [F_sep : is_separable F E]
    (F_inf : infinite F) : ∃ c : F, β ∈ F[α + (algebra_map F E) c * β] :=
begin
    rcases F_sep α with ⟨hα, hf⟩,
    rcases F_sep β with ⟨hβ, hg⟩,
    let f := minimal_polynomial hα,
    let g := minimal_polynomial hβ,
    let f_E := f.map (algebra_map F E),
    let g_E := g.map (algebra_map F E),
    let E' := polynomial.splitting_field g_E,
    let ιFE := algebra_map F E,
    let ιEE' := algebra_map E E',
    let ιFE' := ιEE'.comp(ιFE),
    have key := primitive_element_two_aux ιFE' (ιEE' α) (ιEE' β) (minimal_polynomial.ne_zero hα) (minimal_polynomial.ne_zero hβ) (minimal_polynomial.monic hα) (minimal_polynomial.monic hβ),
    cases key with c hc,
    use c,
    let γ := α+(ιFE c)*β,
    let f' := f_E.comp(polynomial.C γ-(polynomial.C (ιFE c)) * (polynomial.X)),
    let h := euclidean_domain.gcd f' g_E,
    have h_sep : h.separable :=
    begin
        have div := euclidean_domain.gcd_dvd_right f' g_E,
        cases div with p mul,
        dsimp[←h] at mul,
        apply polynomial.separable.of_mul_left,
        rw ←mul,
        exact polynomial.separable.map hg,
    end,
    have h_ne_zero : h ≠ 0 :=
    begin
        intro h_eq_zero,
        rw euclidean_domain.gcd_eq_zero_iff at h_eq_zero,
        apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) h_eq_zero.2,
    end,
    have h_map_separable : (h.map ιEE').separable :=
    begin
        apply polynomial.separable.map,
        exact h_sep,
    end,
    have h_root : h.eval β = 0 :=
    begin
        apply polynomial.gcd_eval_zero,
        rw [polynomial.eval_comp,polynomial.eval_sub,polynomial.eval_mul,polynomial.eval_C,polynomial.eval_C,polynomial.eval_X,add_sub_cancel],
        rw [polynomial.eval_map,←polynomial.aeval_def,minimal_polynomial.aeval],
        rw [polynomial.eval_map,←polynomial.aeval_def,minimal_polynomial.aeval],
    end,
    have h_splits : polynomial.splits (algebra_map E E') h :=
        polynomial.splits_of_splits_of_dvd (algebra_map E E') (polynomial.map_ne_zero (minimal_polynomial.ne_zero hβ)) (polynomial.splitting_field.splits g_E) (euclidean_domain.gcd_dvd_right f' g_E),
    have h_roots : ∀ x ∈ (h.map ιEE').roots, x = algebra_map E E' β :=
    begin
        intros x hx,
        rw polynomial.mem_roots at hx,
        dsimp[polynomial.is_root] at hx,
        rw polynomial.eval_map at hx,
        have f_root : f'.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_left E f' g_E x hx,
        simp only [polynomial.eval₂_comp,polynomial.eval₂_map,polynomial.eval₂_sub,polynomial.eval₂_mul,polynomial.eval₂_C,polynomial.eval₂_X] at f_root,
        replace f_root : _ ∈ (f.map ιFE').roots,
        rw polynomial.mem_roots,
        dsimp[polynomial.is_root],
        rw polynomial.eval_map,
        exact f_root,
        exact polynomial.map_ne_zero (minimal_polynomial.ne_zero hα),
        specialize hc _ f_root,
        have g_root : g_E.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_right E f' g_E x hx,
        simp only [polynomial.eval₂_map] at g_root,
        replace g_root : _ ∈ (g.map ιFE').roots,
        rw polynomial.mem_roots,
        dsimp[polynomial.is_root],
        rw polynomial.eval_map,
        exact g_root,
        exact polynomial.map_ne_zero (minimal_polynomial.ne_zero hβ),
        specialize hc _ g_root,
        by_contradiction,
        specialize hc a,
        apply hc,
        dsimp[ιEE'],
        rw[neg_sub,ring_hom.map_add,←sub_add,←sub_sub,sub_self,zero_sub,neg_add_eq_sub,ring_hom.map_mul,←mul_sub],
        symmetry,
        apply mul_div_cancel,
        rw sub_ne_zero,
        exact a,
        exact polynomial.map_ne_zero h_ne_zero,
    end,
    replace key := primitive_element_two_inf_key_aux ιEE' h_ne_zero h_sep h_root h_splits h_roots,
    let f_Fγ := (f.map(algebra_map F F[γ])).comp(polynomial.C (adjoin_simple.gen F γ)-(polynomial.C ↑c) * (polynomial.X)),
    let g_Fγ := g.map(algebra_map F F[γ]),
    have composition2 : (algebra_map F[γ] E).comp(algebra_map F F[γ]) = algebra_map F E := by ext;refl,
    have f_map : f_Fγ.map(algebra_map F[γ] E) = f' :=
    begin
        dsimp[f_Fγ,f',f_E],
        rw ←composition2,
        rw ←polynomial.map_map,
        set p := f.map(algebra_map F F[γ]),
        dsimp[←p],
        rw polynomial.map_comp (algebra_map F[γ] E) p (polynomial.C (adjoin_simple.gen F γ)-(polynomial.C ↑c) * (polynomial.X)),
        rw [polynomial.map_sub,polynomial.map_C,adjoin_simple.gen_eq_alpha,polynomial.map_mul,polynomial.map_C,polynomial.map_X],
        refl,
    end,
    have g_map : g_Fγ.map(algebra_map F[γ] E) = g_E :=
    begin
        rw polynomial.map_map,
        rw composition2,
    end,
    dsimp[h] at key,
    rw [←f_map,←g_map] at key,
    have swap : euclidean_domain.gcd (f_Fγ.map(algebra_map F[γ] E)) (g_Fγ.map(algebra_map F[γ] E)) = (euclidean_domain.gcd f_Fγ g_Fγ).map(algebra_map F[γ] E),
    convert polynomial.gcd_map (algebra_map F[γ] E),
    rw swap at key,
    set p := euclidean_domain.gcd f_Fγ g_Fγ,
    set k := (p.map(algebra_map F[γ] E)).leading_coeff,
    dsimp[←k] at key,
    rw mul_sub at key,
    rw ←polynomial.C_mul at key,
    have coeff0 : algebra_map F[γ] E (p.coeff 0) = -(k*β) :=
        by rw [←polynomial.coeff_map,key, polynomial.coeff_sub, polynomial.coeff_C_mul, polynomial.coeff_C_zero, polynomial.coeff_X_zero, mul_zero, zero_sub],
    have coeff1 : algebra_map F[γ] E (p.coeff 1) = k :=
    begin
        rw [←polynomial.coeff_map,key,polynomial.coeff_sub,polynomial.coeff_mul_X,polynomial.coeff_C_zero,polynomial.coeff_C],
        change k - 0 = k,
        rw sub_zero,
    end,
    have k_ne_zero : k≠0 :=
    begin
        intro k_eq_zero,
        rw [polynomial.leading_coeff_eq_zero,←polynomial.map_zero (algebra_map F[γ] E)] at k_eq_zero,
        replace k_eq_zero := polynomial.map_injective (algebra_map F[γ] E) (algebra_map F[γ] E).injective k_eq_zero,
        rw euclidean_domain.gcd_eq_zero_iff at k_eq_zero,
        apply polynomial.map_monic_ne_zero (minimal_polynomial.monic hβ) k_eq_zero.2,
    end,
    have last_step : β = algebra_map F[γ] E (-p.coeff 0 / p.coeff 1) :=
        by rw [division_def,ring_hom.map_mul,ring_hom.map_neg,ring_hom.map_inv,coeff0,coeff1,neg_neg,mul_comm,←mul_assoc,inv_mul_cancel k_ne_zero,one_mul],
    change β = ↑(-p.coeff 0 / p.coeff 1) at last_step,
    have h := subtype.mem (-p.coeff 0 / p.coeff 1),
    rw ←last_step at h,
    exact h,
end

/-- Primitive element theorem for adjoining two elements to an infinite field. -/
lemma primitive_element_two_inf (α β : E) (F_sep : is_separable F E)
    (F_inf : infinite F) :  ∃ γ : E, F[α, β] = F[γ] :=
begin
    haveI := inclusion.separable F_sep,
    obtain ⟨c, β_in_Fγ⟩ := primitive_element_two_inf_key α β F_inf,
    let c' := algebra_map F E c,
    let γ := α + c'*β,
    have γ_in_Fγ : γ ∈ F[γ] := adjoin_simple_contains_element F γ,
    have c_in_Fγ : c' ∈ F[γ] := adjoin.field_mem F {γ} c,
    have cβ_in_Fγ : c'*β ∈ F[γ] := is_submonoid.mul_mem c_in_Fγ β_in_Fγ,
    have α_in_Fγ : α ∈ F[γ] := by rw (show α = γ - c'*β, by simp *);
        exact is_add_subgroup.sub_mem F[γ] γ (c'*β) γ_in_Fγ cβ_in_Fγ,
    have αβ_in_Fγ : {α, β} ⊆ F[γ] := λ x hx, by cases hx; cases hx; assumption,
    have Fαβ_sub_Fγ : F[α, β] ⊆ F[γ] := adjoin_subset' F {α, β} αβ_in_Fγ,
    have α_in_Fαβ : α ∈ F[α, β] := adjoin.set_mem F {α, β} ⟨α, set.mem_insert α {β}⟩,
    have β_in_Fαβ : β ∈ F[α, β] := adjoin.set_mem F {α, β} ⟨β, set.mem_insert_of_mem α rfl⟩,
    have c_in_Fαβ : c' ∈ (F[α, β] : set E) := adjoin.field_mem F {α, β} c,
    have cβ_in_Fαβ : c'*β ∈ F[α, β] := is_submonoid.mul_mem c_in_Fαβ β_in_Fαβ,
    have γ_in_Fαβ : γ ∈ F[α, β] := is_add_submonoid.add_mem α_in_Fαβ cβ_in_Fαβ,
    have Fγ_sub_Fαβ : F[γ] ⊆ F[α, β] := adjoin_simple_subset' F γ γ_in_Fαβ,
    exact ⟨γ, set.subset.antisymm Fαβ_sub_Fγ Fγ_sub_Fαβ⟩,
end

universe u

theorem primitive_element_inf_aux (F E : Type u) [field F] [field E] [algebra F E] (F_sep : is_separable F E) (F_findim: finite_dimensional F E) 
    (F_inf : infinite F) (n : ℕ) (hn : findim F E = n) : (∃ α : E, F[α] = (⊤ : set E)) :=
begin
    tactic.unfreeze_local_instances,
    revert F,
    apply n.strong_induction_on,
    clear n,
    intros n ih F hF hFE F_sep F_findim F_inf hn,
    by_cases F_neq_E : base_field_image F E = (⊤ : set E),
    {   exact primitive_element_trivial F_neq_E, },
    {   have : ∃ α : E, α ∉ base_field_image F E :=
        begin
            revert F_neq_E,
            contrapose!,
            exact λ h, set.ext (λ x, ⟨λ _, dec_trivial, λ _, h x⟩),
        end,
        rcases this with ⟨α, hα⟩,
        by_cases h : F[α] = (⊤ : set E),
        {   exact ⟨α, h⟩,   },
        {   have Fα_findim : finite_dimensional F[α] E := adjoin_findim_of_findim F α,
            have Fα_le_n : findim F[α] E < n := by rw ← hn; exact adjoin_dim_lt F hα,
            have Fα_inf : infinite F[α] := adjoin_inf_of_inf F {α} F_inf,
            have Fα_sep : is_separable F[α] E := adjoin_separable F {α},
            obtain ⟨β, hβ⟩ := ih (findim F[α] E) Fα_le_n F[α]
                Fα_sep Fα_findim Fα_inf rfl,
            obtain ⟨γ, hγ⟩ := primitive_element_two_inf α β F_sep F_inf,
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
    have F'_inf : infinite F' := set.infinite_coe_iff.mpr (inclusion.infinite F_inf),
    obtain ⟨α, hα⟩ := primitive_element_inf_aux F' E F'_sep F'_findim F'_inf (findim F' E) rfl,
    exact ⟨α, by simp only [*, adjoin_equals_adjoin_range]⟩,
end

/- Actual primitive element theorem. -/

/-- Primitive element theorem. -/
theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) :
    (∃ α : E, F[α] = (⊤ : set E)) :=
begin
    by_cases F_finite : nonempty (fintype F),
    exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h hfd),
    exact primitive_element_inf hs hfd (not_nonempty_fintype.mp F_finite),
end
