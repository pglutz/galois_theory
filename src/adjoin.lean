import field_theory.subfield
import ring_theory.algebra
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import data.zmod.basic

/- adjoining an element -/

definition adjoin (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : set E :=
field.closure (set.range (algebra_map F E) ∪ {α})

lemma adjoin_contains_alpha (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : α ∈ (adjoin F E α) :=
begin
    apply field.mem_closure,
    right,
    exact set.mem_singleton α,
end

instance adjoin.is_subfield (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : is_subfield (adjoin F E α) := field.closure.is_subfield

instance adjoin.is_algebra (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : algebra F (adjoin F E α) := sorry

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

--The expression "⟨α,adjoin_contains_alpha F E α⟩ : (adjoin F E α)" is a hacky way to get α inside of (adjoin F E α).
--There probably a better way to do this
lemma adjoin_basis (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :
is_basis F (λ n : zmod (minimal_polynomial h).nat_degree, (⟨α,adjoin_contains_alpha F E α⟩ : (adjoin F E α))^(zmod.val n)) :=
begin
    sorry,
end

lemma adjoin_degree (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :
(finite_dimensional.findim F (adjoin F E α)) = (polynomial.nat_degree (minimal_polynomial h)) :=
begin
    have fact := zero_less_than_minimal_polynomial_degree F E α h,
    rw @finite_dimensional.findim_eq_card_basis F (adjoin F E α) _ _ _ _ (@zmod.fintype (minimal_polynomial h).nat_degree fact) _ (adjoin_basis F E α h),
    exact @zmod.card ((minimal_polynomial h).nat_degree) fact,
end