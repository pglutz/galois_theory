import group_theory.coset set_theory.cardinal data.fintype.basic


variables (G : Type*) [set G][group G] 


def subgroup_index (H:subgroup G) := cardinal.mk (quotient_group.quotient H)


lemma index_in_finite_group_is_finite [h_fin : fintype G] (H: subgroup G)[h_dec : decidable_eq (quotient_group.quotient H)]: 
fintype (quotient_group.quotient H):= 

begin
    apply fintype.of_surjective quotient_group.mk,
    intro b,
    apply quot.exists_rep,
    exact h_dec,
    exact h_fin,
end