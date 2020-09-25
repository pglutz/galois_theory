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