import adjoin_set
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import ring_theory.adjoin_root
import data.zmod.basic

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (α : E) (h : is_integral F α)

/-lemma zero_less_than_minimal_polynomial_degree (h : is_integral F α) :
0 < (minimal_polynomial h).nat_degree :=
begin
    by_contradiction,
    apply minimal_polynomial.degree_ne_zero h,
    push_neg at a,
    rw le_zero_iff_eq at a,
    rw ←polynomial.degree_eq_iff_nat_degree_eq (minimal_polynomial.ne_zero h) at a,
    exact a,
end

lemma adjoin_basis (h : is_integral F α) :
is_basis F (λ n : zmod (minimal_polynomial h).nat_degree, (gen F E α)^(zmod.val n)) :=
begin
    sorry,
end

lemma adjoin_degree (h : is_integral F α) :
(finite_dimensional.findim F (adjoin_simple F E α)) = (polynomial.nat_degree (minimal_polynomial h)) :=
begin
    have fact := zero_less_than_minimal_polynomial_degree F E α h,
    rw @finite_dimensional.findim_eq_card_basis F (adjoin_simple F E α) _ _ _ _ (@zmod.fintype (minimal_polynomial h).nat_degree fact) _ (adjoin_basis F E α h),
    exact @zmod.card ((minimal_polynomial h).nat_degree) fact,
end

example (n : ℕ) : α^n ∈ adjoin_simple F E α :=
begin
    exact is_submonoid.pow_mem (adjoin_simple_contains_element F E α),
end-/

noncomputable instance yes_its_a_field_but_lean_want_me_to_give_this_instance_a_name : field (adjoin_root (minimal_polynomial h)) :=
@adjoin_root.field F _ (minimal_polynomial h) (minimal_polynomial.irreducible h)

noncomputable definition quotient_to_adjunction_ring_hom : (adjoin_root (minimal_polynomial h)) →+* (adjoin_simple F α) :=
adjoin_root.lift (algebra_map F (adjoin_simple F α)) (adjoin_simple.gen F α)
begin
    have eval := minimal_polynomial.aeval h,
    dsimp[polynomial.aeval] at eval,
    rw adjoin_simple.composition F α at eval,
    have h := polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F (adjoin_simple F α)) (algebra_map (adjoin_simple F α) E) (adjoin_simple.gen F α),
    rw adjoin_simple.gen_eq_alpha at h,
    rw ←h at eval,
    ext,
    exact eval,
end

noncomputable definition quotient_to_adjunction_algebra_hom : (adjoin_root (minimal_polynomial h)) →ₐ[F] (adjoin_simple F α) := {
    to_fun := (quotient_to_adjunction_ring_hom F α h).to_fun,
    map_one' := (quotient_to_adjunction_ring_hom F α h).map_one',
    map_mul' := (quotient_to_adjunction_ring_hom F α h).map_mul',
    map_zero' := (quotient_to_adjunction_ring_hom F α h).map_zero',
    map_add' := (quotient_to_adjunction_ring_hom F α h).map_add',
    commutes' :=
    begin
        intro r,
        change (quotient_to_adjunction_ring_hom F α h) r = _,
        exact adjoin_root.lift_of,
    end
}

noncomputable def algebra_equiv_of_bij_hom {A : Type*} [ring A] [algebra F A] {B : Type*} [ring B] [algebra F B] (f : A →ₐ[F] B) (h : function.bijective f) : A ≃ₐ[F] B :=
{ .. f, .. equiv.of_bijective _ h }

noncomputable def quotient_to_adjunction : adjoin_root (minimal_polynomial h) ≃ₐ[F] adjoin_simple F α :=
algebra_equiv_of_bij_hom F (quotient_to_adjunction_algebra_hom F α h)
begin
    set f := (algebra_map (adjoin_simple F α) E).comp (quotient_to_adjunction_ring_hom F α h),
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
    dsimp[quotient_to_adjunction_algebra_hom,quotient_to_adjunction_ring_hom],
    rw adjoin_root.lift_of,
    refl,
    intros x hx,
    rw set.mem_singleton_iff at hx,
    rw hx,
    use adjoin_root.root (minimal_polynomial h),
    dsimp[quotient_to_adjunction_algebra_hom,quotient_to_adjunction_ring_hom],
    rw adjoin_root.lift_root,
    refl,
    have key : (adjoin_simple F α) ⊆ set.range(f) := field.closure_subset inclusion,
    intro x,
    specialize key (subtype.mem x),
    cases key with a ah,
    use a,
    ext1,
    assumption,
end

@[simp] lemma quotient_to_adjunction_of_field (f : F) : quotient_to_adjunction F α h f = f :=
begin
    change quotient_to_adjunction_ring_hom F α h f = f,
    exact adjoin_root.lift_of,
end

@[simp] lemma quotient_to_adjunction_of_root : quotient_to_adjunction F α h (adjoin_root.root (minimal_polynomial h)) = adjoin_simple.gen F α :=
begin
    change quotient_to_adjunction_ring_hom F α h (adjoin_root.root (minimal_polynomial h)) = adjoin_simple.gen F α,
    exact adjoin_root.lift_root,
end

lemma quotient_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
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
end