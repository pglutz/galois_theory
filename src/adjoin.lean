import field_theory.subfield
import ring_theory.algebra
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import data.zmod.basic

/- adjoining an element -/

definition adjoin (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : set E :=
field.closure (set.range (algebra_map F E) ∪ {α})

lemma zero_less_than_minimal_polynomial_degree (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :
0 < (minimal_polynomial h).nat_degree :=
begin
    by_contradiction,
    apply minimal_polynomial.degree_ne_zero h,
    push_neg at a,
    rw le_zero_iff_eq at a,
    rw ←polynomial.degree_eq_iff_nat_degree_eq (minimal_polynomial.ne_zero h) at a,
    exact a,
end

lemma adjoin_basis (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :
is_basis F (λ n : zmod (minimal_polynomial h).nat_degree, α^(zmod.val n)) :=
begin
    sorry,
end

lemma adjoin_degree (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :
(finite_dimensional.findim F E) = (polynomial.nat_degree (minimal_polynomial h)) :=
begin
    have fact := zero_less_than_minimal_polynomial_degree F E α h,
    have h₀ := @zmod.fintype (minimal_polynomial h).nat_degree fact,
    have h₁ := @finite_dimensional.findim_eq_card_basis F E _ _ _ _ h₀ _ (adjoin_basis F E α h),
    rw h₁,
    have h₂ := @zmod.card ((minimal_polynomial h).nat_degree) fact,
    --uhhh, so why doesn't "exact h₂" work???
    sorry
end