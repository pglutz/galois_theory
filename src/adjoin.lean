--import subfield_stuff
import field_theory.subfield
import field_theory.separable
import field_theory.tower
import group_theory.subgroup
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import ring_theory.adjoin_root
import data.zmod.basic

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

def adjoin : set E := field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin.field_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
field.mem_closure (or.inl (set.mem_range_self x))

lemma adjoin.field_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
    intros x hx,
    cases hx with f hf,
    rw ←hf,
    exact adjoin.field_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.field_mem F S x⟩}

lemma adjoin.set_mem (x : S) : ↑x ∈ adjoin F S :=
field.mem_closure (or.inr (subtype.mem x))

lemma adjoin.set_subset : S ⊆ adjoin F S :=
λ x hx, adjoin.set_mem F S ⟨x,hx⟩

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨↑x, adjoin.set_mem F S x⟩}

lemma adjoin.mono (T : set E) (h : S ⊆ T) : adjoin F S ⊆ adjoin F T :=
field.closure_mono (set.union_subset (set.subset_union_left _ _) (set.subset_union_of_subset_right h _))

instance adjoin.is_subfield : is_subfield (adjoin F S) := field.closure.is_subfield

lemma adjoin_contains_field_as_subfield (F : set E) {HF : is_subfield F} : F ⊆ adjoin F S :=
λ x hx, adjoin.field_mem F S ⟨x, hx⟩

lemma adjoin_contains_subset {T : set E} {H : T ⊆ S} : T ⊆ adjoin F S :=
begin
    intros x hx,
    exact adjoin.set_mem F S ⟨x,H hx⟩,
end

instance adjoin.is_algebra : algebra F (adjoin F S) := {
    smul := λ x y, ⟨algebra_map F E x, adjoin.field_mem F S x⟩ * y,
    to_fun := λ x, ⟨algebra_map F E x, adjoin.field_mem F S x⟩,
    map_one' := by simp only [ring_hom.map_one];refl,
    map_mul' := λ x y, by simp only [ring_hom.map_mul];refl,
    map_zero' := by simp only [ring_hom.map_zero];refl,
    map_add' := λ x y, by simp only [ring_hom.map_add];refl,
    commutes' := λ x y, by rw mul_comm,
    smul_def' := λ x y, rfl,
}

def adjoin_as_submodule : submodule F E := {
    carrier := adjoin F S,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ a b, is_add_submonoid.add_mem,
    smul_mem' :=
    begin
        intros a b hb,
        rw algebra.smul_def,
        exact is_submonoid.mul_mem (adjoin.field_mem F S a) hb,
    end
}

definition adjoin_as_submodule_equiv : (adjoin F S) ≃ₗ[F] (adjoin_as_submodule F S) := {
    to_fun := λ x, x,
    map_add' := λ x y, rfl,
    map_smul' :=
    begin
        intros x y,
        ext1,
        change _ = x • ↑y,
        rw algebra.smul_def,
        rw algebra.smul_def,
        refl,
    end,
    inv_fun := λ x, x,
    left_inv := λ x, rfl,
    right_inv := λ x, rfl,
}

lemma adjoin_subset {T : set E} [is_subfield T] (HF : set.range (algebra_map F E) ⊆ T) (HS : S ⊆ T) : adjoin F S ⊆ T :=
begin
    apply field.closure_subset,
    rw set.union_subset_iff,
    exact ⟨HF,HS⟩,
end

/-- If S ⊆ F[T] then F[S] ⊆ F[T] -/
lemma adjoin_subset' {T : set E} (HT : S ⊆ adjoin F T) : adjoin F S ⊆ adjoin F T :=
adjoin_subset F S (adjoin.field_subset F T) HT

lemma set_range_subset {T₁ T₂ : set E} [is_subfield T₁] [is_subfield T₂] {hyp : T₁ ⊆ T₂} :
set.range (algebra_map T₁ E) ⊆ T₂ :=
begin
    intros x hx,
    cases hx with f hf,
    rw ←hf,
    cases f with t ht,
    exact hyp ht,
end

/- The range of the embedding of F into E is equal to the range of the inclusion embedding of
    range(F → E) into E. -/
lemma algebra_map_twice : set.range (algebra_map (set.range (algebra_map F E)) E) = set.range (algebra_map F E) :=
begin
    ext, split,
    {   rintros ⟨⟨y, ⟨z, rfl⟩⟩, rfl⟩,
        exact ⟨z, rfl⟩,
    },
    {   exact λ hx, ⟨⟨x, hx⟩, rfl⟩, },
end

/- Adjoining S to F is the same as adjoining S to the range of the embedding of F into E. -/
lemma adjoin_equals_adjoin_range : adjoin F S = adjoin (set.range (algebra_map F E)) S :=
by simp only [adjoin, algebra_map_twice]

lemma adjoin_contains_field_subset {F : set E} {HF : is_subfield F} {T : set E} {HT : T ⊆ F} : T ⊆ adjoin F S :=
λ x hx, adjoin.field_mem F S ⟨x,HT hx⟩

lemma adjoin_twice (T : set E) : adjoin (adjoin F S) T = adjoin F (S ∪ T) :=
begin
    apply set.eq_of_subset_of_subset,
    apply adjoin_subset,
    apply set_range_subset,
    apply adjoin_subset,
    apply adjoin.field_subset,
    apply adjoin_contains_subset,
    apply set.subset_union_left,
    apply adjoin_contains_subset,
    apply set.subset_union_right,
    apply adjoin_subset,
    transitivity adjoin F S,
    apply adjoin.field_subset,
    apply adjoin_subset,
    apply adjoin_contains_field_subset,
    apply adjoin.field_subset,
    apply adjoin_contains_field_subset,
    apply adjoin.set_subset,
    apply set.union_subset,
    apply adjoin_contains_field_subset,
    apply adjoin.set_subset,
    apply adjoin.set_subset,
end

lemma adjoin.composition : (algebra_map F E) = (algebra_map (adjoin F S) E).comp (algebra_map F (adjoin F S)) :=
begin
    ext,
    refl,
end

instance adjoin_algebra_tower : is_scalar_tower F (adjoin F S) E := {
    smul_assoc :=
    begin
        intros x y z,
        rw algebra.smul_def,
        rw algebra.smul_def,
        rw algebra.smul_def,
        rw ring_hom.map_mul,
        rw mul_assoc,
        refl,
    end
}

lemma adjoin_separable [F_sep : is_separable F E] : is_separable (adjoin F S) E :=
begin
    intro x,
    cases F_sep x with hx hs,
    have hx' : is_integral (adjoin F S) x := is_integral_of_is_scalar_tower x hx,
    use hx',
    have key : (minimal_polynomial hx') ∣ (minimal_polynomial hx).map(algebra_map F (adjoin F S)),
    apply minimal_polynomial.dvd,
    dsimp[polynomial.aeval],
    rw polynomial.eval₂_map,
    rw ← adjoin.composition,
    apply minimal_polynomial.aeval,
    cases key with q hq,
    apply polynomial.separable.of_mul_left,
    rw ←hq,
    exact polynomial.separable.map hs,
end

variables (α : E) (h : is_integral F α)

-- Let's try out this notation?
notation K`[`:std.prec.max_plus β`]` := adjoin K (@singleton _ _ set.has_singleton β)
notation K`[`:std.prec.max_plus β `,` γ`]` := adjoin K {β,γ}
-- This notation would allow us to write F[α, β] for adjoin_simple (adjoin_simple F α) β
-- notation K`⟨`L:(foldr `,` (x M, adjoin_simple M x) K `⟩`) := L 
-- notation K`[[` binders `]]`s:(scoped β, set.insert β) := adjoin K s

lemma adjoin_simple_contains_element : α ∈ F[α] :=
adjoin.set_mem F {α} (⟨α,set.mem_singleton α⟩ : ({α} : set E))

instance adjoin_is_algebra : algebra F F[α] :=
adjoin.is_algebra F {α}

def adjoin_simple_as_submodule : submodule F E :=
adjoin_as_submodule F {α}

definition adjoin_simple_as_submodule_equiv : F[α] ≃ₗ[F] (adjoin_simple_as_submodule F α) :=
adjoin_as_submodule_equiv F {α}

/-- A subfield of E that contains F and α also contains F[α] -/
lemma adjoin_simple_subset {T : set E} [is_subfield T] (HF : set.range (algebra_map F E) ⊆ T) (Hα : α ∈ T) : F[α] ⊆ T :=
adjoin_subset F {α} HF (set.singleton_subset_iff.mpr Hα)

/-- If α is in F[T] then F[α] ⊆ F[T] -/
lemma adjoin_simple_subset' {T : set E} (HT : α ∈ adjoin F T) : F[α] ⊆ adjoin F T :=
adjoin_subset' F {α} (set.singleton_subset_iff.mpr HT)

--generator of F(α)
def adjoin_simple.gen : F[α] := ⟨α, adjoin_simple_contains_element F α⟩

lemma adjoin_simple.gen_eq_alpha : algebra_map F[α] E (adjoin_simple.gen F α) = α := rfl

/-- If the generator is not in the inclusion of F in E then it's also not in the inclusion of
    F in F[α]. -/
lemma adjoin_simple_gen_nontrivial {α : E} (hα : α ∉ set.range (algebra_map F E)) :
    adjoin_simple.gen F α ∉ set.range (algebra_map F F[α]) :=
begin
    revert hα,
    contrapose!,
    rintros ⟨x, hx⟩,
    injections_and_clear,
    use x, assumption,
end

lemma adjoin_simple_twice (β : E) : F[α][β] = adjoin F {α,β} :=
adjoin_twice _ _ _

def submodule_restrict_field (α : E) (p : submodule F[α] E) : submodule F E := {
    carrier := p.carrier,
    zero_mem' := p.zero_mem',
    add_mem' := p.add_mem',
    smul_mem' :=
    begin
        intros c x hx,
        rw algebra.smul_def,
        rw adjoin.composition F {α},
        rw ring_hom.comp_apply,
        rw ←algebra.smul_def,
        exact p.smul_mem' _ hx,
    end
}

instance adjoin_simple_algebra_tower : is_scalar_tower F (F[α]) E :=
adjoin_algebra_tower F {α}

section
open finite_dimensional

/-- If a subset of a set is infinite then the set is infinite. -/
lemma inf_of_subset_inf {X : Type*} {s : set X} {t : set X} (hst : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, ht.subset hst) hs

/-- If E is a finite extension of F then it is also a finite extension of F adjoin alpha. -/
instance adjoin_findim_of_findim [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional F[α] E :=
begin
    rw iff_fg,
    rw submodule.fg_iff_finite_dimensional,
    cases (finite_dimensional.exists_is_basis_finite F E) with B hB,
    have key : submodule.span F[α] B = ⊤,
    {   ext,
        simp only [submodule.mem_top, iff_true],
        have hx : x ∈ submodule.span F (set.range coe),
        {   rw hB.1.2,
            exact submodule.mem_top, },
        rw submodule.mem_span,
        intros p hp,
        rw submodule.mem_span at hx,
        apply hx (submodule_restrict_field F α p),
        rw subtype.range_coe,
        exact hp, },
    rw ← key,
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

/-- If F is infinite then its inclusion into E is infinite. -/
lemma inclusion.infinite (hF : infinite F) : (set.range (algebra_map F E)).infinite :=
begin
    apply set.infinite_coe_iff.mp,
    apply infinite.of_injective (set.range_factorization (algebra_map F E)),
    exact subtype.coind_injective (λ (a : F), set.mem_range_self a) ((algebra_map F E).injective),
end

lemma adjoin_inf_of_inf (S : set E) (hF : infinite F) : infinite (adjoin F S) :=
begin
    rw adjoin_equals_adjoin_range,
    apply set.infinite_coe_iff.mpr,
    exact inf_of_subset_inf (adjoin_contains_field_as_subfield S (set.range (algebra_map F E))) (inclusion.infinite F hF),
end

end

variables {E' : Type*} [field E'] [algebra F E'] (α' : E') (hα' : (minimal_polynomial h).eval₂ (algebra_map F E') α' = 0)

noncomputable def quotient_embedding_ring_hom :
(adjoin_root (minimal_polynomial h)) →+* E' :=
adjoin_root.lift (algebra_map F E') α' hα'

noncomputable def quotient_embedding : (adjoin_root (minimal_polynomial h)) →ₐ[F] E' := {
    to_fun := (quotient_embedding_ring_hom F α h α' hα').to_fun,
    map_one' := (quotient_embedding_ring_hom F α h α' hα').map_one',
    map_mul' := (quotient_embedding_ring_hom F α h α' hα').map_mul',
    map_zero' := (quotient_embedding_ring_hom F α h α' hα').map_zero',
    map_add' := (quotient_embedding_ring_hom F α h α' hα').map_add',
    commutes' :=
    begin
        intro r,
        change (quotient_embedding_ring_hom F α h α' hα') r = _,
        exact adjoin_root.lift_of,
    end
}

@[simp] lemma quotient_embedding_of_field (f : F) : quotient_embedding F α h α' hα' f = algebra_map F E' f :=
begin
    change quotient_embedding_ring_hom F α h α' hα' f = algebra_map F E' f,
    exact adjoin_root.lift_of,
end

@[simp] lemma quotient_embedding_of_root : quotient_embedding F α h α' hα' (adjoin_root.root (minimal_polynomial h)) = α' :=
begin
    change quotient_embedding_ring_hom F α h α' hα' (adjoin_root.root (minimal_polynomial h)) = α',
    exact adjoin_root.lift_root,
end

noncomputable instance yes_its_a_field_but_lean_want_me_to_give_this_instance_a_name : field (adjoin_root (minimal_polynomial h)) :=
@adjoin_root.field F _ (minimal_polynomial h) (minimal_polynomial.irreducible h)

lemma adjoin_simple.eval_gen : polynomial.eval₂ (algebra_map F F[α]) (adjoin_simple.gen F α) (minimal_polynomial h) = 0 :=
begin
    ext,
    have eval := minimal_polynomial.aeval h,
    dsimp[polynomial.aeval] at eval,
    rw adjoin.composition F {α} at eval,
    have h := polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F F[α]) (algebra_map F[α] E) (adjoin_simple.gen F α),
    rw adjoin_simple.gen_eq_alpha at h,
    rw ←h at eval,
    exact eval,
end

noncomputable def quotient_to_adjunction_algebra_hom : (adjoin_root (minimal_polynomial h)) →ₐ[F] F[α] :=
quotient_embedding F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h)

noncomputable def algebra_equiv_of_bij_hom' {A : Type*} [ring A] [algebra F A] {B : Type*} [ring B] [algebra F B] (f : A →ₐ[F] B) (h : function.bijective f) : A ≃ₐ[F] B :=
{ .. f, .. equiv.of_bijective _ h }

noncomputable def quotient_to_adjunction : adjoin_root (minimal_polynomial h) ≃ₐ[F] F[α] :=
algebra_equiv_of_bij_hom' F (quotient_to_adjunction_algebra_hom F α h)
begin
    set f := (algebra_map F[α] E).comp((quotient_to_adjunction_algebra_hom F α h) : (adjoin_root (minimal_polynomial h)) →+* F[α]),
    split,
    apply ring_hom.injective,
    have inclusion : (set.range (algebra_map F E) ∪ {α}) ⊆ set.range(f),
    rw set.union_subset_iff,
    split,
    intros x hx,
    rw set.mem_range at hx,
    cases hx with y hy,
    rw ←hy,
    use y,
    dsimp[f,quotient_to_adjunction_algebra_hom],
    rw quotient_embedding_of_field F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h) y,
    refl,
    intros x hx,
    rw set.mem_singleton_iff at hx,
    rw hx,
    use adjoin_root.root (minimal_polynomial h),
    dsimp[f,quotient_to_adjunction_algebra_hom],
    rw quotient_embedding_of_root F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h),
    refl,
    have key : F[α] ⊆ set.range(f) := field.closure_subset inclusion,
    intro x,
    specialize key (subtype.mem x),
    cases key with a ah,
    use a,
    ext1,
    assumption,
end

@[simp] lemma quotient_to_adjunction_of_field (f : F) : quotient_to_adjunction F α h f = f :=
quotient_embedding_of_field F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h) f

@[simp] lemma quotient_to_adjunction_of_root : quotient_to_adjunction F α h (adjoin_root.root (minimal_polynomial h)) = adjoin_simple.gen F α :=
quotient_embedding_of_root F α h (adjoin_simple.gen F α) (adjoin_simple.eval_gen F α h)

noncomputable def adjunction_embedding : F[α] →ₐ[F] E' :=
(quotient_embedding F α h α' hα').comp((quotient_to_adjunction F α h).symm)

@[simp] lemma adjunction_embedding_of_field (f : F) : adjunction_embedding F α h α' hα' f = algebra_map F E' f :=
begin
    dsimp[adjunction_embedding],
    rw ←quotient_to_adjunction_of_field,
    rw alg_equiv.symm_apply_apply,
    rw quotient_embedding_of_field,
end

@[simp] lemma adjunction_embedding_of_root : adjunction_embedding F α h α' hα' (adjoin_simple.gen F α) = α' :=
begin
    dsimp[adjunction_embedding],
    rw ←quotient_to_adjunction_of_root,
    rw alg_equiv.symm_apply_apply,
    rw quotient_embedding_of_root,
end

variables (ϕ ψ : (adjoin F S) →+* E')

def adjoin_equalizer : set (adjoin F S) :=
(λ f, ϕ f = ψ f)

instance to_adjunction_embedding_equalizer_is_subfield : is_subfield (adjoin_equalizer F S ϕ ψ) := {
    zero_mem :=
    begin
        change ϕ 0 = ψ 0,
        rw ring_hom.map_zero,
        rw ring_hom.map_zero,
    end,
    add_mem :=
    begin
        intros a b ha hb,
        change ϕ a = ψ a at ha,
        change ϕ b = ψ b at hb,
        change ϕ (a + b) = ψ (a + b),
        rw ring_hom.map_add,
        rw ring_hom.map_add,
        rw ha,
        rw hb,
    end,
    neg_mem :=
    begin
        intros a ha,
        change ϕ a = ψ a at ha,
        change ϕ (-a) = ψ (-a),
        rw ring_hom.map_neg,
        rw ring_hom.map_neg,
        rw ha,
    end,
    one_mem :=
    begin
        change ϕ 1 = ψ 1,
        rw ring_hom.map_one,
        rw ring_hom.map_one,
    end,
    mul_mem :=
    begin
        intros a b ha hb,
        change ϕ a = ψ a at ha,
        change ϕ b = ψ b at hb,
        change ϕ (a * b) = ψ (a * b),
        rw ring_hom.map_mul,
        rw ring_hom.map_mul,
        rw ha,
        rw hb,
    end,
    inv_mem :=
    begin
        intros a ha,
        change ϕ a = ψ a at ha,
        change ϕ a⁻¹ = ψ a⁻¹,
        rw ring_hom.map_inv,
        rw ring_hom.map_inv,
        rw ha,
    end
}

instance to_adjunction_embedding_equalizer_coe_is_subfield : is_subfield ((coe '' adjoin_equalizer F S ϕ ψ) : set E) := {
    zero_mem := ⟨0,⟨is_add_submonoid.zero_mem,rfl⟩⟩,
    add_mem :=
    begin
        intros a b ha hb,
        cases ha with a' ha',
        cases hb with b' hb',
        rw[←ha'.2,←hb'.2],
        exact ⟨a'+b',⟨is_add_submonoid.add_mem ha'.1 hb'.1,rfl⟩⟩,
    end,
    neg_mem :=
    begin
        intros a ha,
        cases ha with a' ha',
        rw ←ha'.2,
        exact ⟨-a',⟨is_add_subgroup.neg_mem ha'.1,rfl⟩⟩,
    end,
    one_mem := ⟨1,⟨is_submonoid.one_mem,rfl⟩⟩,
    mul_mem :=
    begin
        intros a b ha hb,
        cases ha with a' ha',
        cases hb with b' hb',
        rw[←ha'.2,←hb'.2],
        exact ⟨a'*b',⟨is_submonoid.mul_mem ha'.1 hb'.1,rfl⟩⟩,
    end,
    inv_mem :=
    begin
        intros a ha,
        cases ha with a' ha',
        rw ←ha'.2,
        exact ⟨a'⁻¹,⟨is_subfield.inv_mem ha'.1,rfl⟩⟩,
    end
}

lemma ring_hom_determined_by_generators (hF : ∀ f : F, ϕ f = ψ f) (hS : ∀ s : S, ϕ s = ψ s) : ϕ = ψ :=
begin
    suffices key : adjoin F S ⊆ coe '' adjoin_equalizer F S ϕ ψ,
    ext,
    specialize key (subtype.mem x),
    cases key with y hy,
    rw ←subtype.ext hy.2,
    exact hy.1,
    dsimp[adjoin],
    rw field.closure_subset_iff,
    rw set.union_subset_iff,
    split,
    intros x hx,
    cases hx with y hy,
    exact ⟨↑y,⟨hF y,hy⟩⟩,
    intros x hx,
    exact ⟨⟨x,adjoin.set_mem F S ⟨x,hx⟩⟩,⟨hS ⟨x,hx⟩,rfl⟩⟩,
end

variable (ι : F[α] →ₐ[F] E') 

lemma adjunction_embedding_classification_aux : polynomial.eval₂ (algebra_map F E') (ι (adjoin_simple.gen F α)) (minimal_polynomial h) = 0 :=
begin
    have key2 : ((ι : F[α] →+* E').comp(algebra_map F F[α]) = algebra_map F E'),
    ext,
    simp only [alg_hom.coe_to_ring_hom, function.comp_app, ring_hom.coe_comp, alg_hom.commutes],
    rw ←key2,
    change polynomial.eval₂ ((ι : F[α] →+* E').comp(algebra_map F F[α])) ((ι : F[α] →+* E') (adjoin_simple.gen F α)) (minimal_polynomial h) = 0,
    rw ←polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F F[α]) (ι : F[α] →+* E') (adjoin_simple.gen F α),
    rw adjoin_simple.eval_gen,
    simp only [alg_hom.coe_to_ring_hom, alg_hom.map_zero],
end

noncomputable def to_adjunction_embedding : F[α] →ₐ[F] E' :=
adjunction_embedding F α h (ι (adjoin_simple.gen F α)) (adjunction_embedding_classification_aux F α h ι)

--proves that every map F(α) → E' is comes from adjunction_embedding
lemma adjunction_embedding_classification : ι = to_adjunction_embedding F α h ι :=
begin
    have key := ring_hom_determined_by_generators F {α} (ι : F[α] →+* E') (to_adjunction_embedding F α h ι : F[α] →+* E'),
    have hF : ∀ f : F, ι f = to_adjunction_embedding F α h ι f,
    intro f,
    dsimp[to_adjunction_embedding],
    rw adjunction_embedding_of_field,
    exact alg_hom.commutes ι f,
    specialize key hF,
    rw ring_hom.ext_iff at key,
    rw alg_hom.ext_iff,
    apply key,
    intro s,
    have h' : (↑s : adjoin F {α}) = adjoin_simple.gen F α,
    ext,
    cases s with s hs,
    exact set.mem_singleton_iff.2 hs,
    rw h',
    dsimp[to_adjunction_embedding],
    rw adjunction_embedding_of_root,
end

/-lemma quotient_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
    sorry
end

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root (minimal_polynomial h))) = (minimal_polynomial h).nat_degree :=
begin
    sorry
end

lemma adjunction_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
    sorry
end

lemma adjunction_degree : (finite_dimensional.findim F (adjoin_simple F α)) = (minimal_polynomial h).nat_degree :=
begin
    have algequiv : adjoin_root (minimal_polynomial h) ≃ₐ[F] adjoin_simple F α := quotient_to_adjunction F α h,
    have linequiv : adjoin_root (minimal_polynomial h) ≃ₗ[F] adjoin_simple F α,
    fconstructor,
    exact algequiv.to_fun,
    exact algequiv.map_add,
    intro c,
    intro x,
    change algequiv (c * x) = ((algebra_map F (adjoin_simple F α) c) * (algequiv x)),
    rw[algequiv.map_mul,←algequiv.commutes],
    refl,
    exact algequiv.inv_fun,
    exact algequiv.left_inv,
    exact algequiv.right_inv,
    rw ← @linear_equiv.findim_eq F (adjoin_root (minimal_polynomial h)) _ _ _ (adjoin_simple F α) _ _ linequiv (quotient_degree_finite F α h),
    exact quotient_degree F α h,
end-/