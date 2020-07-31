import adjoin_simple
import ring_theory.adjoin_root

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (hα : is_integral F α)

-- I think the following definition and lemma should replace the theorem below
def quotient_to_adjunction' : adjoin_root (minimal_polynomial hα) ≃+* adjoin_simple F α := sorry

lemma root_to_adjoined : ↑ (quotient_to_adjunction' F E α hα (adjoin_root.root (minimal_polynomial hα))) = α := sorry

/-   lemma bijective_ring_homorphism_is_an_isomorphism (R:Type*) [ring R] (S:Type*) [ring S] (φ:R→ S)-/
theorem adjunction_equiv_to_quotient  (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α): 
∃ (f:polynomial F) (hom: (adjoin_root f) →+* (adjoin_simple F α)), 
(irreducible f ∧ ∃ (isom: (adjoin_root f) ≃+* (adjoin_simple F α )),(isom.to_fun=hom ∧ ↑ (isom.to_fun (adjoin_root.root f)) = α )) := 
begin
    let f:=minimal_polynomial h,
    use f,
    use quotient_to_adjunction_hom F α h,
    split,
    exact minimal_polynomial.irreducible h,
    sorry
end
