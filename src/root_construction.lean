import adjoin_simple
import ring_theory.adjoin_root
import algebra.category.CommRing.basic
import data.equiv.basic
/-   lemma bijective_ring_homorphism_is_an_isomorphism (R:Type*) [ring R] (S:Type*) [ring S] (φ:R→ S)-/



variables {A : Type*} [ring A]
variables {B : Type*} [ring B]

noncomputable def ring_equiv_of_bij_hom (f : A →+* B) (h : function.bijective f) : A ≃+* B :=
{ map_mul' := by apply ring_hom.map_mul,
  map_add' := by apply ring_hom.map_add,
  ..show A ≃ B, by exact equiv.of_bijective _ h }

theorem adjunction_equiv_to_quotient  (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α): 
∃ (f:polynomial F) (hom: (adjoin_root f) →+* (adjoin_simple F E α )), 
(irreducible f ∧ ∃ (isom: (adjoin_root f) ≃+* (adjoin_simple F E α )),(isom.to_fun=hom ∧ ↑ (isom.to_fun (adjoin_root.root f)) = α )) := 
begin
    let f:=minimal_polynomial h,
    use f,
    use adjoin_root_hom_to_adjoin_simple F E α h,
    split,
    exact minimal_polynomial.irreducible h,
    sorry
    
    


end




lemma ring_closure_equals_field_closure (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α): 
ring.closure (set.range (algebra_map F E) ∪ {α })=adjoin_simple F E α :=

begin
    have eq_ring_closure: set.range((adjoin_root_hom_to_E F E α h))=ring.closure (set.range ⇑(algebra_map F E) ∪ {α }),
    
    /-
    apply set.eq_of_subset_of_subset,
    dsimp[adjoin_simple,adjoin],
    apply field.ring_closure_subset,
    dsimp[adjoin_simple,adjoin],
    
    have is_field: field(ring.closure (set.range ⇑(algebra_map F E) ∪ {α})),
    -/


end




