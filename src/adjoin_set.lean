import field_theory.subfield
import ring_theory.algebra
import group_theory.subgroup

/- adjoining a set -/

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

definition adjoin : set E :=
field.closure (set.range (algebra_map F E) ∪ S)

lemma adjoin_contains_field (x : F) : algebra_map F E x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    left,
    exact set.mem_range_self x,
end

instance : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin_contains_field F S x⟩}

lemma adjoin_contains_element (x : S) : ↑x ∈ (adjoin F S) :=
begin
    apply field.mem_closure,
    right,
    exact subtype.mem x,
end

instance adjoin.is_subfield : is_subfield (adjoin F S) := field.closure.is_subfield

instance adjoin.has_scalar : has_scalar F (adjoin F S) := {
    smul := λ x y, ⟨algebra_map F E x, adjoin_contains_field F S x⟩ * y,
}

instance adjoin.is_algebra : algebra F (adjoin F S) := {
    to_fun := λ x, ⟨algebra_map F E x, adjoin_contains_field F S x⟩,
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
        intros x y,
        rw mul_comm,
    end,
    smul_def' :=
    begin
        intros x y,
        refl,
    end
}

variable (α : E)

definition adjoin_simple : set E := adjoin F {α}

lemma adjoin_simple_contains_field (x : F) : algebra_map F E x ∈ (adjoin_simple F α) :=
adjoin_contains_field F {α} x

instance : has_coe_t F (adjoin_simple F α) :=
{coe := λ x, ⟨algebra_map F E x, adjoin_simple_contains_field F α x⟩}

lemma adjoin_simple_contains_element : α ∈ adjoin_simple F α :=
adjoin_contains_element F {α} (⟨α,set.mem_singleton α⟩ : ({α} : set E))

instance adjoin_simple.is_subfield : is_subfield (adjoin_simple F α) :=
adjoin.is_subfield F {α}

instance adjoin_is_algebra : algebra F (adjoin_simple F α) :=
adjoin.is_algebra F {α}

--generator of F(α)
definition adjoin_simple.gen : (adjoin_simple F α) := ⟨α, adjoin_simple_contains_element F α⟩

lemma adjoin_simple.gen_eq_alpha : algebra_map (adjoin_simple F α) E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple.composition : (algebra_map F E) = (algebra_map (adjoin_simple F α) E).comp (algebra_map F (adjoin_simple F α)) :=
begin
    ext,
    refl,
end