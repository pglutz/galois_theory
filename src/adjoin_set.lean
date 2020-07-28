import field_theory.subfield
import ring_theory.algebra

/- adjoining a set -/

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (S : set E)

definition adjoin : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin_contains_field (x : F) : algebra_map F E x ∈ (adjoin F E S) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

lemma adjoin_contains_element (x : S) : ↑x ∈ (adjoin F E S) :=
begin
    apply field.mem_closure,
    right,
    exact subtype.mem x,
end

instance adjoin.is_subfield : is_subfield (adjoin F E S) := field.closure.is_subfield

instance adjoin.has_scalar : has_scalar F (adjoin F E S) := {
    smul := λ x y, ⟨algebra_map F E x, adjoin_contains_field F E S x⟩ * y,
}

instance adjoin.is_algebra : algebra F (adjoin F E S) := {
    to_fun := λ x, ⟨algebra_map F E x, adjoin_contains_field F E S x⟩,
    map_one' :=
    begin
        simp only [ring_hom.map_one],
        refl,
    end,
    map_mul' :=
    begin
        intros x y,
        simp only [ring_hom.map_mul],
        refl,
    end,
    map_zero' :=
    begin
        simp only [ring_hom.map_zero],
        refl,
    end,
    map_add' :=
    begin
        intros x y,
        simp only [ring_hom.map_add],
        refl,
    end,
    commutes' :=
    begin
        sorry,
    end,
    smul_def' :=
    begin
        sorry,
    end
}

variable (α : E)

definition adjoin_simple : set E := adjoin F E {α}

lemma adjoin_simple_contains_field (x : F) : algebra_map F E x ∈ (adjoin_simple F E α) :=
adjoin_contains_field F E {α} x

lemma adjoin_simple_contains_element : α ∈ (adjoin_simple F E α) :=
adjoin_contains_element F E {α} (⟨α,set.mem_singleton α⟩ : ({α} : set E))

instance adjoin_simple.is_subfield : is_subfield (adjoin_simple F E α) :=
adjoin.is_subfield F E {α}

instance adjoin_is_algebra : algebra F (adjoin_simple F E α) :=
adjoin.is_algebra F E {α}