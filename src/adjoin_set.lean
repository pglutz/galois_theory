import field_theory.subfield
import ring_theory.algebra
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import data.zmod.basic

/- adjoining a set -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (S : set E)

definition adjoin (S : set E) : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin_contains_field (S : set E) (x : F) : algebra_map F E x ∈ (adjoin F E S) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

lemma adjoin_set_contains_element (S : set E) (x : S) : ↑x ∈ (adjoin F E S) :=
begin
    apply field.mem_closure,
    right,
    exact subtype.mem x,
end

instance adjoin.is_subfield (S : set E) : is_subfield (adjoin F E S) := field.closure.is_subfield

instance adjoin.is_algebra (S : set E) : algebra F (adjoin F E S) := sorry