import adjoin_set
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import ring_theory.adjoin_root
import data.zmod.basic

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E)

--generator of F(α)
definition gen : (adjoin_simple F E α) := ⟨α, adjoin_simple_contains_element F E α⟩

lemma zero_less_than_minimal_polynomial_degree (h : is_integral F α) :
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
end

lemma algebra_map_composition : (algebra_map F E) = (algebra_map (adjoin_simple F E α) E).comp (algebra_map F (adjoin_simple F E α)) :=
begin
    ext,
    refl,
end

lemma algebra_map_gen_equals_alpha : algebra_map (adjoin_simple F E α) E (gen F E α) = α := rfl

noncomputable definition the_map (h : is_integral F α) : (adjoin_root (minimal_polynomial h)) →+* (adjoin_simple F E α) :=
adjoin_root.lift (algebra_map F (adjoin_simple F E α)) (gen F E α)
begin
    have eval := minimal_polynomial.aeval h,
    dsimp[polynomial.aeval] at eval,
    rw algebra_map_composition F E α at eval,
    have h := polynomial.hom_eval₂ (minimal_polynomial h) (algebra_map F (adjoin_simple F E α)) (algebra_map (adjoin_simple F E α) E) (gen F E α),
    rw algebra_map_gen_equals_alpha at h,
    rw ←h at eval,
    ext,
    exact eval,
end