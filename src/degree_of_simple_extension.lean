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

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (p : polynomial F) (h : p ≠ 0)

def module_quotient_map : polynomial F →ₐ[F] adjoin_root p :=
{ to_fun := (adjoin_root.mk p).to_fun,
  map_zero' := (adjoin_root.mk p).map_zero,
  map_add' := (adjoin_root.mk p).map_add,
  map_one' := (adjoin_root.mk p).map_one,
  map_mul' := (adjoin_root.mk p).map_mul,
  commutes' := λ _, rfl, }

def canonical_basis: {n: ℕ| n<polynomial.nat_degree p }→ adjoin_root p:= λ (n:{n: ℕ| n<polynomial.nat_degree p }), adjoin_root.mk p (polynomial.X^(n:ℕ))

lemma canonical_basis_is_basis : is_basis F (canonical_basis F p) :=
begin
  split,
  { apply linear_independent_iff.mpr,
    intros f hf,
    dsimp only [canonical_basis] at hf,
    dsimp only [finsupp.total] at hf,
    rw finsupp.lsum_apply at hf,
    dsimp [finsupp.sum] at hf,
    simp only [linear_map.id_coe, id.def] at hf,
    change f.support.sum (λ a, (f a) • (module_quotient_map F p (X ^ ↑a))) = 0 at hf,
    simp only [←alg_hom.map_smul] at hf,
    haveI : is_add_monoid_hom (module_quotient_map F p) := sorry,
    rw finset.sum_hom at hf,
    sorry,
     },
  {},
end


 




lemma adjunction_basis : is_basis F (canonical_basis F p):=
begin
  let degree:=polynomial.nat_degree p,
  let x:polynomial F:= polynomial.X,
  let S:= {n: ℕ| n<degree},
  let ν:= λ (n:S), (x^(n:ℕ)),
  let η := (adjoin_root.mk p)∘ν,
  have nonneg: degree=0 ∨ degree>0,
  exact nat.eq_zero_or_pos degree,
  cases nonneg with zero_deg pos_deg,
  {sorry},
  
  have comp: η = (adjoin_root.mk p) ∘ ν := rfl,
  { unfold is_basis,
    split,
    { apply linear_independent_iff.2,
      intros l eq_zero,
      have decomp: (finsupp.total S (adjoin_root p) F η) l=(adjoin_root.mk p) ((finsupp.total ↥S (polynomial F) F ν) l),
      { rw comp,
        have is_fin':finset ↥S := finset.univ,
        symmetry,
        let algebra_1 :=algebra_map F (adjoin_root p),
        let algebra_2 :=algebra_map F (polynomial F),
        have adjoin_root_is_module_map:(adjoin_root.mk p).to_fun=(module_quotient_map F p).to_fun:=by simpa,

        have eq_1:(adjoin_root.mk p) ((finsupp.total ↥S (polynomial F) F ν) l) = (module_quotient_map F p)((finsupp.total ↥S (polynomial F) F ν) l):=
        by simpa[adjoin_root_is_module_map],

        have eq_2: (finsupp.total ↥S (adjoin_root p) F ((adjoin_root.mk p) ∘ ν)) l = (finsupp.total ↥S (adjoin_root p) F ((module_quotient_map F p) ∘ ν)) l:=
        by simpa[adjoin_root_is_module_map],

        have eq_3: (module_quotient_map F p)((finsupp.total ↥S (polynomial F) F ν) l) = (finsupp.total ↥S (adjoin_root p) F ((module_quotient_map F p) ∘ ν)) l:=sorry,
        --dsimp[finsupp.total],
        --simp[finsupp.lmap_domain_total],
        --exact finsupp.lmap_domain_total F,
        --simp_rw[finsupp.lmap_domain_total],
        sorry,
        
        

      },
      sorry,
    },
    { sorry, },
  },

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

lemma adjunction_degree_finite : finite_dimensional F (adjoin_root p) :=
begin
  let degree:=polynomial.nat_degree p,
  let x:polynomial F:= polynomial.X,
  let S:= {n: ℕ| n<degree},
  let η := λ (n:S), adjoin_root.mk p (x^(n:ℕ)),
  let ν:= λ (n:S), (x^(n:ℕ)),
  have comp: η = (adjoin_root.mk p) ∘ ν := rfl,

  have is_fin:fintype S,
  exact set.fintype_lt_nat degree,

  have basis:is_basis F η,
  { unfold is_basis,
    split,
    { apply linear_independent_iff.2,
      intros l eq_zero,
      have decomp: (finsupp.total ↥S (adjoin_root p) F η) l=(adjoin_root.mk p) ((finsupp.total ↥S (polynomial F) F ν) l),
      { rw comp,
        have is_fin':finset ↥S := finset.univ,
        symmetry,
        let algebra_1 :=algebra_map F (adjoin_root p),
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

lemma quotient_degree : (finite_dimensional.findim F (adjoin_root p)) = p.nat_degree :=

begin
    sorry

end

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
by {rw [← linear_equiv.findim_eq (adjoin_root_equiv_fin_fun_degree F p h), findim_fin_fun]}

lemma adjoin_root_dim_eq_degree (p : polynomial F) (h : p ≠ 0) :
  dim F (adjoin_root p) = nat_degree p :=
by rw [← linear_equiv.dim_eq (adjoin_root_equiv_fin_fun_degree F p h), dim_fin_fun]
