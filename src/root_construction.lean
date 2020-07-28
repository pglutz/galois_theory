import adjoin_simple
import ring_theory.adjoin_root

theorem adjunction_equiv_to_quotient  (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : 
∃ (f:polynomial F) (isom: (adjoin_root f) ≃+* (adjoin_simple F E α )), (irreducible f ∧ ↑ (isom.to_fun (adjoin_root.root f)) = α ) := sorry 