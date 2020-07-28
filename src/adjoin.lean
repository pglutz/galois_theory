import field_theory.subfield
import ring_theory.algebra
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import data.zmod.basic

/- adjoining an element -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E)

definition adjoin_set (S : set E) : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

definition adjoin_element : set E :=
adjoin_set F E {α}

lemma adjoin_contains_field (x : F) : algebra_map F E x ∈ (adjoin_element F E α) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

lemma adjoin_contains_alpha : α ∈ (adjoin_element F E α) :=
begin
    apply field.mem_closure,
    right,
    exact set.mem_singleton α,
end

--generator of F(α)
definition gen : (adjoin_element F E α) := ⟨α, adjoin_contains_alpha F E α⟩

instance adjoin.is_subfield : is_subfield (adjoin_element F E α) := field.closure.is_subfield

instance adjoin.is_algebra : algebra F (adjoin_element F E α) := sorry

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
(finite_dimensional.findim F (adjoin_element F E α)) = (polynomial.nat_degree (minimal_polynomial h)) :=
begin
    have fact := zero_less_than_minimal_polynomial_degree F E α h,
    rw @finite_dimensional.findim_eq_card_basis F (adjoin_element F E α) _ _ _ _ (@zmod.fintype (minimal_polynomial h).nat_degree fact) _ (adjoin_basis F E α h),
    exact @zmod.card ((minimal_polynomial h).nat_degree) fact,
end