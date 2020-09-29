-- import subfield_stuff
-- import group_theory.subgroup
-- import field_theory.minimal_polynomial
-- import linear_algebra.dimension
-- import linear_algebra.finite_dimensional
-- import linear_algebra.basis
-- import ring_theory.adjoin_root
-- import data.zmod.basic
-- import data.polynomial.basic
-- import adjoin

import ring_theory.adjoin_root
import linear_algebra.finite_dimensional
import field_theory.minimal_polynomial

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable
open vector_space polynomial finite_dimensional

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E) (α : E) (h : is_integral F α)



lemma smul3 (p : polynomial F) (c_1 : F) (f : polynomial F) :
  (adjoin_root.mk p) (c_1 • f) = c_1 • ((adjoin_root.mk p) f):=
by simpa [algebra.smul_def, ring_hom.map_mul]

noncomputable def module_quotient_map (p : polynomial F): polynomial F →ₗ[F] adjoin_root p :=
{ to_fun:=(adjoin_root.mk p).to_fun, 
  map_add':=(adjoin_root.mk p).map_add,
  map_smul':=smul3 F p }

lemma adjunction_degree_finite : finite_dimensional F (adjoin_root (minimal_polynomial h)) :=
begin
  let minimal:=minimal_polynomial h,
  let degree:=polynomial.nat_degree minimal,
  let x:polynomial F:= polynomial.X,
  let S:= {n: ℕ| n<degree},
  let η := λ (n:S), adjoin_root.mk minimal (x^(n:ℕ)),
  let ν:= λ (n:S), (x^(n:ℕ)),
  have comp: η = (adjoin_root.mk minimal) ∘ ν := rfl,

  have is_fin:fintype S,
  exact set.fintype_lt_nat degree,

  have basis:is_basis F η,
  { unfold is_basis,
    split,
    { apply linear_independent_iff.2,
      intros l eq_zero,
      have decomp: (finsupp.total ↥S (adjoin_root minimal) F η) l=(adjoin_root.mk minimal) ((finsupp.total ↥S (polynomial F) F ν) l),
      { rw comp,
        have is_fin':finset ↥S := finset.univ,
        symmetry,
        let algebra_1 :=algebra_map F (adjoin_root (minimal_polynomial h)),
        let algebra_2 :=algebra_map F (polynomial F),
        have degree_is_positive: 0<degree := sorry,
        sorry,
      },
      sorry,
    },
    { sorry, },
  },
  sorry,
end

/-  apply finite_dimensional.of_finite_basis, -/

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root (minimal_polynomial h))) = (minimal_polynomial h).nat_degree :=

begin
    sorry

end

-- I have written an outline of a different way of proving the theorems above, which
-- does not involve working with bases. The basic idea is to show that (adjoin_root p)
-- is isomorphic to F^(degree p) (which is expressed in mathlib as (fin (nat_degree p) → F)).
-- Also, I think this can be proved for all nonzero polynomials, not just those which happen
-- to be the minimal polynomial for something. Of course, with an arbitrary polynomial p,
-- F[x]/p is not a field, but that doesn't matter if you just care about the vector space
-- structure.
--
-- Here's my proposed strategy for proving the isomorphism:
-- 1) First construct the map from (fin (nat_degree p) → F) to adjoin_root p
--    Hopefully this should be easy because there's a map from (fin (nat_degree p) → F)
--    to polynomial F and so it should give a map on the quotient.
-- 2) Show that this map is linear. Maybe it's better to first show that the map to
--    polynomial F is linear and automatically get a linear map by composing with the
--    quotient.
-- 3) Show that this map is a bijection.begin
-- 4) Use the theorem linear_equiv.of_bijective to finish.

lemma adjoin_root_equiv_fin_fun_degree (p : polynomial F) (h : p ≠ 0) :
  (fin (nat_degree p) → F) ≃ₗ[F] adjoin_root p :=
begin
  sorry,
end

lemma adjoin_root_finite_dimensional (p : polynomial F) (h : p ≠ 0) :
  finite_dimensional F (adjoin_root p) :=
linear_equiv.finite_dimensional (adjoin_root_equiv_fin_fun_degree F p h)

lemma adjoin_root_findim_eq_degree (p : polynomial F) (h : p ≠ 0) :
  findim F (adjoin_root p) = nat_degree p :=
by rw [← linear_equiv.findim_eq (adjoin_root_equiv_fin_fun_degree F p h), findim_fin_fun]

lemma adjoin_root_dim_eq_degree (p : polynomial F) (h : p ≠ 0) :
  dim F (adjoin_root p) = nat_degree p :=
by rw [← linear_equiv.dim_eq (adjoin_root_equiv_fin_fun_degree F p h), dim_fin_fun]
