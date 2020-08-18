import adjoin
import linear_algebra.finite_dimensional
import linear_algebra.basic
import data.set.finite
import field_theory.tower
import algebra.gcd_monoid
import field_theory.splitting_field

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

/-- If a subset of a set is infinite then the set is infinite. -/
lemma inf_of_subset_inf {X : Type*} {s : set X} {t : set X} (hst : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, ht.subset hst) hs

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

/-- The set of roots of a polynomial f in a field E where f is a polynomial in F and F ⊆ E. -/
def roots {F : Type*} [field F] (f : polynomial F) (E : Type*) [field E] [algebra F E]  :=
{α : E | polynomial.eval₂ (algebra_map F E) α f = 0}

/-- The definition of roots agrees with the mathlib definition. -/
lemma roots_eq_map_roots {F : Type*} [field F] (f : polynomial F) (E : Type*) [field E] [algebra F E]
    (hf : f ≠ 0) (f_monic : polynomial.monic f) : roots f E = ↑(polynomial.map (algebra_map F E) f).roots :=
begin
    set f' := polynomial.map (algebra_map F E) f with hf',
    have f'_ne_zero : f' ≠ 0 := polynomial.map_monic_ne_zero f_monic,
    ext,
    change x ∈ roots f E ↔ x ∈ f'.roots,
    rw [polynomial.mem_roots f'_ne_zero, polynomial.is_root, ← polynomial.eval₂_eq_eval_map],
    refl,
end

/-- The set of roots in E of a nonzero polynomial f over F is a finite set. -/
lemma roots_is_fintype {F : Type*} [field F] (f : polynomial F) (E : Type*) [field E] [algebra F E] 
    (hf : f ≠ 0) (f_monic : polynomial.monic f) : fintype (roots f E) :=
begin
    rw roots_eq_map_roots f E hf f_monic,
    exact finset_coe.fintype (polynomial.map (algebra_map F E) f).roots,
end

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

/- Trivial case of the primitive element theorem. -/

/-- Primitive element theorem when F = E. -/
lemma primitive_element_trivial (F : set E) [hF : is_subfield F] (F_eq_E : F = (⊤ : set E)) :
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
    apply field_mem_adjoin,
end

/- Primitive element theorem for finite fields. -/

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
theorem primitive_element_fin [fintype F] (hfd : finite_dimensional F E) :
    ∃ α : E, F[α] = (⊤ : set E) := @primitive_element_fin_aux F _ E _ _ (finite_of_findim_over_finite F)

/- Primitive element theorem for infinite fields. -/

lemma primitive_element_two_aux (α β : E) (f g : polynomial F) (F_inf : infinite F) (hf : f ≠ 0) (hg : g ≠ 0) (f_monic : polynomial.monic f) (g_monic : polynomial.monic g) :
    ∃ c : F, ∀ (α' : roots f E) (β' : roots g E), ↑β' ≠ β → (algebra_map F E c) ≠ -(α' - α)/(β' - β) :=
begin
    let ι := algebra_map F E,
    let s := {c : F | ∃ (α' : roots f E) (β' : roots g E), ↑β' ≠ β ∧ ι c = -(α' - α)/(β' - β)},
    have s_fin : fintype s :=
    begin
        by_cases s_nonempty : nonempty s,
        let x := s_nonempty.some,
        let r : (roots f E) × (roots g E) → s :=
        begin
            rintros ⟨α', β'⟩,
            by_cases hβ : ↑β' = β,
            use x,
            let c' : E := -(α' - α)/(β' - β),
            by_cases hc' : c' ∈ set.range ι,
            set c := reverse_inclusion_ring_hom F E ⟨c', hc'⟩ with h,
            have hc : c ∈ s :=
            begin
                use [α', β', hβ],
                rw h,
                change ((inclusion_isomorphism F E).to_fun ((inclusion_isomorphism F E).inv_fun ⟨c', hc'⟩) : E) = -(↑α' - α)/(↑β' - β),
                rw (inclusion_isomorphism F E).right_inv,
                refl,
            end,
            use ⟨c, hc⟩,
            use x,
        end,
        have r_surjective : function.surjective r :=
        begin
            rintros ⟨c, ⟨α', β', hβ', hc⟩⟩,
            use ⟨α', β'⟩,
            dsimp only [r],
            split_ifs with hβ h,
            {   exfalso, exact hβ' hβ, },
            {   ext,
                dsimp,
                rw ← reverse_inclusion_of_field F E c,
                unfold_coes,
                funext,
                simp only [*, ring_hom.to_fun_eq_coe, subtype.val_eq_coe],
            },
            { exfalso, exact h ⟨c, hc⟩, },
        end,
        have roots_prod_fin : fintype ((roots f E) × (roots g E)) := @prod.fintype (roots f E) (roots g E)
            (roots_is_fintype f E hf f_monic) (roots_is_fintype g E hg g_monic),
        exact @fintype.of_surjective _ _ _ roots_prod_fin r r_surjective,
        exact ⟨∅, λ x, false.rec _ (not_nonempty_iff_imp_false.mp s_nonempty x)⟩,
    end,
    let s' := set.finite.to_finset (nonempty.intro s_fin),
    obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s',
    rw set.finite.mem_to_finset at hc,
    dsimp at hc,
    push_neg at hc,
    exact ⟨c, hc⟩,
end

lemma primitive_element_two_inf_key_aux (β : F) (h : polynomial F) (h_ne_zero : h ≠ 0) (h_sep : h.separable)
(h_root : h.eval β = 0) (h_splits : polynomial.splits (algebra_map F E) h)
(h_roots : ∀ x : roots h E, ↑x = algebra_map F E β) :
h = (polynomial.C (polynomial.leading_coeff h)) * (polynomial.X - polynomial.C β) :=
begin
    have h_map_separable : (h.map(algebra_map F E)).separable :=
    begin
        apply polynomial.separable.map,
        exact h_sep,
    end,
    rw polynomial.splits_iff_exists_multiset at h_splits,
    cases h_splits with s hs,
    have s_elements : ∀ x ∈ s, x = algebra_map F E β :=
    begin
        intros x hx,
        have is_root : polynomial.eval₂ (algebra_map F E) x h = 0,
        rw polynomial.eval₂_eq_eval_map,
        rw hs,
        rw polynomial.eval_mul,
        cases multiset.exists_cons_of_mem hx with y hy,
        rw hy,
        rw multiset.map_cons,
        simp only [polynomial.eval_X, multiset.prod_cons, polynomial.eval_C, zero_mul, polynomial.eval_mul, polynomial.eval_sub, mul_zero, sub_self],
        exact h_roots ⟨x,is_root⟩,
    end,
    replace s_elements : ∀ x ∈ multiset.map (λ (a : E), polynomial.X - polynomial.C a) s, x = polynomial.X - polynomial.C (algebra_map F E β) :=
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
    have hf : ¬is_unit (polynomial.X - polynomial.C (algebra_map F E β)) :=
    begin
        rw polynomial.is_unit_iff_degree_eq_zero,
        rw polynomial.degree_X_sub_C,
        exact dec_trivial,
    end,
    have map_injective := polynomial.map_injective (algebra_map F E) (algebra_map F E).injective,
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

lemma primitive_element_two_inf_key (F : set E) [is_subfield F] (α β : E) [F_sep : is_separable F E]
    (F_inf : F.infinite) : ∃ c : F, β ∈ F[α + c*β] :=
begin
    rcases F_sep α with ⟨hα, hf⟩,
    rcases F_sep β with ⟨hβ, hg⟩,
    let f := minimal_polynomial hα,
    let g := minimal_polynomial hβ,
    let f_E := f.map (algebra_map F E),
    let g_E := g.map (algebra_map F E),
    let E' := polynomial.splitting_field g_E,
    let ι := algebra_map E E',
    have composition1 : (algebra_map E E').comp (algebra_map F E) = algebra_map F E' := by ext;refl,
    have key : ∃ c : F, ∀ α' : roots f E', ∀ β' : roots g E', ↑β' ≠ ι β → ι c ≠ -(α'-ι α)/(β'-ι β) :=
    primitive_element_two_aux F (ι α) (ι β) f g (set.infinite_coe_iff.mpr F_inf) (minimal_polynomial.ne_zero hα) (minimal_polynomial.ne_zero hβ) (minimal_polynomial.monic hα) (minimal_polynomial.monic hβ),
    cases key with c hc,
    use c,
    let γ := α+c*β,
    let f' := f_E.comp(polynomial.C γ-(polynomial.C ↑c) * (polynomial.X)),
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
    have h_map_separable : (h.map ι).separable :=
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
    have h_roots : ∀ x : roots h E', ↑x = algebra_map E E' β :=
    begin
        intro x,
        cases x with x hx,
        dsimp[roots] at hx,
        have f_root : f'.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_left E f' g_E x hx,
        simp only [polynomial.eval₂_comp,polynomial.eval₂_map,polynomial.eval₂_sub,polynomial.eval₂_mul,polynomial.eval₂_C,polynomial.eval₂_X,composition1] at f_root,
        change _ ∈ roots f E' at f_root,
        specialize hc ⟨_,f_root⟩,
        have g_root : g_E.eval₂ (algebra_map E E') x = 0 := polynomial.gcd_root_right E f' g_E x hx,
        simp only [polynomial.eval₂_map,composition1] at g_root,
        change _ ∈ roots g E' at g_root,
        specialize hc ⟨_,g_root⟩,
        by_contradiction,
        specialize hc a,
        apply hc,
        dsimp[ι],
        rw[neg_sub,ring_hom.map_add,←sub_add,←sub_sub,sub_self,zero_sub,neg_add_eq_sub,ring_hom.map_mul,←mul_sub],
        symmetry,
        apply mul_div_cancel,
        rw sub_ne_zero,
        exact a,
    end,
    replace key := primitive_element_two_inf_key_aux E β h h_ne_zero h_sep h_root h_splits h_roots,
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
lemma primitive_element_two_inf (F : set E) [is_subfield F] (α β : E) (F_sep : is_separable F E)
    (F_inf : F.infinite) :  ∃ γ : E, F[α, β] = F[γ] :=
begin
    obtain ⟨c, β_in_Fγ⟩ := primitive_element_two_inf_key F α β F_inf,
    let γ := α + c*β,
    have γ_in_Fγ : γ ∈ F[γ] := adjoin_simple_contains_element F γ,
    have c_in_Fγ : ↑c ∈ F[γ] := adjoin_simple_contains_field F γ c,
    have cβ_in_Fγ : ↑c*β ∈ F[γ] := is_submonoid.mul_mem c_in_Fγ β_in_Fγ,
    have α_in_Fγ : α ∈ F[γ] := by rw (show α = γ - ↑c*β, by simp *);
        exact is_add_subgroup.sub_mem F[γ] γ (↑c*β) γ_in_Fγ cβ_in_Fγ,
    have αβ_in_Fγ : {α, β} ⊆ F[γ] := λ x hx, by cases hx; cases hx; assumption,
    have Fαβ_sub_Fγ : F[α, β] ⊆ F[γ] := adjoin_subset' F {α, β} αβ_in_Fγ,
    have α_in_Fαβ : α ∈ F[α, β] := set_mem_adjoin F {α, β} ⟨α, set.mem_insert α {β}⟩,
    have β_in_Fαβ : β ∈ F[α, β] := set_mem_adjoin F {α, β} ⟨β, set.mem_insert_of_mem α rfl⟩,
    have c_in_Fαβ : ↑c ∈ (F[α, β] : set E) := field_mem_adjoin F {α, β} c,
    have cβ_in_Fαβ : ↑c*β ∈ F[α, β] := is_submonoid.mul_mem c_in_Fαβ β_in_Fαβ,
    have γ_in_Fαβ : γ ∈ F[α, β] := is_add_submonoid.add_mem α_in_Fαβ cβ_in_Fαβ,
    have Fγ_sub_Fαβ : F[γ] ⊆ F[α, β] := adjoin_simple_subset' F γ γ_in_Fαβ,
    exact ⟨γ, set.subset.antisymm Fαβ_sub_Fγ Fγ_sub_Fαβ⟩,
end

def submodule_restrict_field (α : E) (p : submodule F[α] E) : submodule F E := {
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
    finite_dimensional F[α] E :=
begin
    rw iff_fg,
    rw submodule.fg_iff_finite_dimensional,
    cases (finite_dimensional.exists_is_basis_finite F E) with B hB,
    have key : submodule.span F[α] B = ⊤,
    ext,
    simp only [submodule.mem_top, iff_true],
    have hx : x ∈ submodule.span F (set.range coe),
    rw hB.1.2,
    exact submodule.mem_top,
    rw submodule.mem_span,
    intros p hp,
    rw submodule.mem_span at hx,
    apply hx (submodule_restrict_field F α p),
    rw subtype.range_coe,
    exact hp,
    rw ←key,
    apply finite_dimensional.span_of_finite F[α] hB.2,
end

instance adjoin_findim_of_findim_base [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional F F[α] :=
begin
    have h := finite_dimensional.finite_dimensional_submodule (adjoin_simple_as_submodule F α),
    exact linear_equiv.finite_dimensional (adjoin_simple_as_submodule_equiv F α).symm,
end

/-- If the field extension E has an element not in the base field F then the degree of E over F is
    greater than 1. -/
lemma algebra_findim_lt [hF : finite_dimensional F E] : (∃ x : E, x ∉ set.range (algebra_map F E)) →
    1 < findim F E :=
begin
    contrapose!,
    intros E_dim x,
    have : 0 < findim F E := findim_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩,
    replace E_dim : findim F E = 1 := by omega,
    set s : set E := {1} with hs,
    have : fintype s := unique.fintype,
    have s_lin_ind : linear_independent F (coe : s → E) := linear_independent_singleton one_ne_zero,
    have s_card : s.to_finset.card = findim F E := by change s.to_finset.card with 1; rw E_dim,
    obtain ⟨_, s_spans⟩ := set_is_basis_of_linear_independent_of_card_eq_findim s_lin_ind s_card,
    have x_in_span_one : x ∈ submodule.span F s :=
    begin
        rw subtype.range_coe at s_spans,
        rw s_spans,
        exact submodule.mem_top,
    end,
    obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_one,
    exact ⟨a, by rw [← ha, algebra.smul_def, mul_one]⟩,
end

/-- Adjoining an element from outside of F strictly decreases the degree of a finite extension. -/
lemma adjoin_dim_lt [hF : finite_dimensional F E] {α : E} (hα : α ∉ set.range (algebra_map F E)) :
    findim F[α] E < findim F E :=
begin
    rw ← findim_mul_findim F F[α] E,
    have : 0 < findim F[α] E := findim_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩,
    have : adjoin_simple.gen F α ∉ set.range (algebra_map F F[α]) := adjoin_simple_gen_nontrivial F hα,
    have : findim F F[α] > 1 := algebra_findim_lt F (by tauto),
    nlinarith,
end

/-- Adjoining an element from outside of F strictly decreases the degree of the extension if it's finite. -/
lemma adjoin_dim_lt_subfield (F : set E) [hF : is_subfield F] [F_findim : finite_dimensional F E] (α : E) (hα : α ∉ F) :
    findim F[α] E < findim F E := by apply adjoin_dim_lt; finish

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
    {   exact primitive_element_trivial F F_neq_E, },
    {   have : ∃ α : E, α ∉ F :=
        begin
            revert F_neq_E,
            contrapose!,
            exact λ h, set.ext (λ x, ⟨λ _, dec_trivial, λ _, h x⟩),
        end,
        rcases this with ⟨α, hα⟩,
        by_cases h : F[α] = (⊤ : set E),
        {   exact ⟨α, h⟩,   },
        {   have Fα_findim : finite_dimensional F[α] E := adjoin_findim_of_findim F α,
            have Fα_le_n : findim F[α] E < n := by rw ← hn; exact adjoin_dim_lt_subfield F α hα,
            have Fα_inf : F[α].infinite :=
                inf_of_subset_inf (adjoin_contains_field_as_subfield {α} F) F_inf,
            have Fα_sep : is_separable F[α] E := begin
                intro x,
                cases F_sep x with hx hs,
                have hx' : is_integral F[α] x := is_integral_of_is_scalar_tower x hx,
                use hx',
                have key : (minimal_polynomial hx') ∣ (minimal_polynomial hx).map(algebra_map F F[α]),
                apply minimal_polynomial.dvd,
                dsimp[polynomial.aeval],
                rw polynomial.eval₂_map,
                rw ←adjoin_simple.composition,
                apply minimal_polynomial.aeval,
                cases key with q hq,
                apply polynomial.separable.of_mul_left,
                rw ←hq,
                exact polynomial.separable.map hs,
            end,
            obtain ⟨β, hβ⟩ := ih (findim F[α] E) Fα_le_n F[α]
                Fα_sep Fα_findim Fα_inf rfl,
            obtain ⟨γ, hγ⟩ := primitive_element_two_inf F α β F_sep F_inf,
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
    have F'_findim : finite_dimensional F' E := finite_dimensional.trans (set.range (algebra_map F E)) F E,
    have F'_inf : F'.infinite := set.infinite_coe_iff.mp (infinite.of_injective (set.range_factorization (algebra_map F E)) (subtype.coind_injective set.mem_range_self (algebra_map F E).injective)),
    obtain ⟨α, hα⟩ := primitive_element_inf_aux F' F'_sep F'_findim F'_inf (findim F' E) rfl,
    exact ⟨α, by simp only [*, adjoin_simple_equals_adjoin_simple_range]⟩,
end

/- Actual primitive element theorem. -/

/-- Primitive element theorem. -/
theorem primitive_element (hs : is_separable F E)  (hfd : finite_dimensional F E) :
    (∃ α : E, F[α] = (⊤ : set E)) :=
begin
    by_cases F_finite : nonempty (fintype F),
    exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_fin F _ E _ _ h hfd),
    exact primitive_element_inf F hs hfd (not_nonempty_fintype.mp F_finite),
end

-- lemma primitive_element_trivial' (F_eq_E : base_field_image F E = (⊤ : set E)) :
--     ∃ α : E, F[α] = (⊤ : set E) :=
-- begin
--     use 0,
--     ext,
--     split,
--     intro _,
--     exact dec_trivial,
--     rw ← F_eq_E,
--     rintros ⟨x, rfl⟩,
--     apply adjoin_contains_field,
-- end


-- theorem primitive_element_inf_aux' (F_sep : is_separable F E) (F_findim: finite_dimensional F E) 
--     (F_inf : infinite F) (n : ℕ) (hn : findim F E = n) : (∃ α : E, F[α] = (⊤ : set E)) :=
-- begin
--     tactic.unfreeze_local_instances,
--     revert F,
--     apply n.strong_induction_on,
--     clear n,
--     intros n ih F hF hFE F_sep F_findim F_inf hn,
--     by_cases F_neq_E : base_field_image F E = (⊤ : set E),
--     -- {   exact primitive_element_trivial' F F_neq_E, },
--     -- {   have : ∃ α : E, α ∉ base_field_image F E :=
--     --     begin
--     --         revert F_neq_E,
--     --         contrapose!,
--     --         exact λ h, set.ext (λ x, ⟨λ _, dec_trivial, λ _, h x⟩),
--     --     end,
--     --     rcases this with ⟨α, hα⟩,
--     --     by_cases h : F[α] = (⊤ : set E),
--     --     {   exact ⟨α, h⟩,   },
--     --     {   have Fα_findim : finite_dimensional F[α] E := adjoin_findim_of_findim F α,
--     --         have Fα_le_n : findim F[α] E < n := by rw ← hn; exact adjoin_dim_lt_subfield F α hα,
--     --         have Fα_inf : F[α].infinite :=
--     --             inf_of_subset_inf (adjoin_contains_field_as_subfield {α} F) F_inf,
--     --         have Fα_sep : is_separable F[α] E := adjoin_simple_is_separable F F_sep α,
--     --         obtain ⟨β, hβ⟩ := ih (findim F[α] E) Fα_le_n F[α]
--     --             Fα_sep Fα_findim Fα_inf rfl,
--     --         obtain ⟨γ, hγ⟩ := primitive_element_two_inf F α β F_sep F_inf,
--     --         rw [adjoin_simple_twice, hγ] at hβ,
--     --         exact ⟨γ, hβ⟩,
--     --     },
--     -- },
-- end