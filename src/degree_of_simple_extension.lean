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

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)(α : E) (h : is_integral F α)



lemma smul3:
∀  (p:polynomial F) (c_1 : F)  (f: polynomial F), (adjoin_root.mk p) (c_1 • f) = c_1 • ((adjoin_root.mk p) f):=λ p c f, by simpa[algebra.smul_def,ring_hom.map_mul]



noncomputable def module_quotient_map (p:polynomial F): polynomial F →ₗ[F] adjoin_root p :=

{
    
    to_fun:=(adjoin_root.mk p).to_fun, 
    map_add':=(adjoin_root.mk p).map_add,
    map_smul':=smul3 F p    
}

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
    have is_fin':finset ↥S,
    exact finset.univ,
    symmetry,
    let algebra_1 :=algebra_map F (adjoin_root (minimal_polynomial h)),
    let algebra_2 :=algebra_map F (polynomial F),
    have degree_is_positive: 0<degree,
    
    
 

    sorry
    

    

end
→ₗ



/-  apply finite_dimensional.of_finite_basis, -/

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root (minimal_polynomial h))) = (minimal_polynomial h).nat_degree :=

begin
    sorry

end