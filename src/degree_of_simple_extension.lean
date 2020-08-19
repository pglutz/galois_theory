import subfield_stuff
import group_theory.subgroup
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import linear_algebra.basis
import ring_theory.adjoin_root
import data.zmod.basic
import data.polynomial.basic
import adjoin

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)(α : E) (h : is_integral F α)

instance algebra_is_vector_space (V:Type*)[add_comm_group V][semiring V][algebra F V]: vector_space F V:=sorry



lemma adjunction_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
    let minimal:=minimal_polynomial h,
    let degree:=polynomial.nat_degree minimal,
    let x:polynomial F:= polynomial.X,
    let S:= {n: ℕ| n<degree},
    let η := λ (n:S), adjoin_root.mk minimal (x^(n:ℕ)),
    let ν:= λ (n:S), (x^(n:ℕ)),
    have comp: η = (adjoin_root.mk minimal) ∘ ν, 
    exact rfl,

    
    have is_fin:fintype S,
    exact set.fintype_lt_nat degree,

    have basis:is_basis F η,
    unfold is_basis,
    split,
    apply linear_independent_iff.2,
    intros l eq_zero,
    have decomp: (finsupp.total ↥S (adjoin_root minimal) F η) l=(adjoin_root.mk minimal) ((finsupp.total ↥S (polynomial F) F ν) l),
    rw comp,
    
    
    /-have is_ideal:=ideal.quotient.eq_zero_iff_mem.1 eq_zero,-/


    

end


/-  apply finite_dimensional.of_finite_basis, -/

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root (minimal_polynomial h))) = (minimal_polynomial h).nat_degree :=

begin
    sorry

end
