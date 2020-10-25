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

lemma polynomial.degree_mod_lt {R : Type*} [field R] (p q : polynomial R)
  (h : p ≠ 0) : (q % p).degree < p.degree :=
begin
  exact euclidean_domain.mod_lt q h,
end


variables {F : Type*} [field F] (p : polynomial F)

def module_map : polynomial.degree_lt F (p.nat_degree) →ₗ[F] adjoin_root p := {
  to_fun := λ q, adjoin_root.mk p q,
  map_add' := λ _ _, ring_hom.map_add _ _ _,
  map_smul' := λ _ _, by simpa [algebra.smul_def, ring_hom.map_mul],
}

lemma module_map_injective : function.injective (module_map p) :=
begin
  rw is_add_group_hom.injective_iff,
  intros q hq,
  change ideal.quotient.mk _ _ = 0 at hq,
  rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton] at hq,
  cases hq with r hr,
  cases q with q hq,
  rw submodule.coe_mk at hr,
  rw [submodule.mk_eq_zero, hr],
  rw [mem_degree_lt, hr, degree_mul] at hq,
  clear hr q,
  by_cases hp : (p = 0),
  { rw [hp, zero_mul] },
  by_cases hr : (r = 0),
  { rw [hr, mul_zero] },
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hr, ←with_bot.coe_add, with_bot.coe_lt_coe] at hq,
  exfalso,
  nlinarith,
end

lemma module_map_surjective' (h : p ≠ 0) : function.surjective (module_map p) :=
begin
  intro q,
  obtain ⟨q', hq'⟩ : ∃ q', adjoin_root.mk p q' = q := ideal.quotient.mk_surjective q,
  use (q' % p),
  { rw [mem_degree_lt, ← degree_eq_nat_degree h],
    exact euclidean_domain.mod_lt q' h, },
  { change adjoin_root.mk p (q' % p) = q,
    symmetry,
    rw [← hq', adjoin_root.mk, ideal.quotient.eq, ideal.mem_span_singleton'],
    exact ⟨q' / p, by rw [eq_sub_iff_add_eq, mul_comm, euclidean_domain.div_add_mod]⟩, },
end

lemma module_map_surjective [polynomial.degree p>0]: function.surjective (module_map p) :=
begin
  intro q,
  have s : function.surjective (adjoin_root.mk p) := ideal.quotient.mk_surjective,
  have t : ∃ g : polynomial F, (adjoin_root.mk p) g = q := s q,
  cases t with preimage salem,
  use (preimage % p),
  have u:(preimage % p).degree<p.degree,
  { rw polynomial.mod_def,
    have w:=ne_zero_of_degree_gt _inst_2,
    { have alpha: p * C ((p.leading_coeff)⁻¹)=normalize p,
      { dsimp,
        rw polynomial.coe_norm_unit_of_ne_zero w},
        rw alpha,
        have beta:p.degree=(normalize p).degree,
          rw [polynomial.degree_normalize],
          rw beta,
          apply polynomial.degree_mod_by_monic_lt,
          exact monic_normalize w,
        exact monic.ne_zero (polynomial.monic_normalize w), }, },
  have gamma:p.degree=p.nat_degree,
    { exact polynomial.degree_eq_nat_degree (ne_zero_of_degree_gt _inst_2), },
  rw gamma at u,
  exact mem_degree_lt.mpr u,

  --exact monic.ne_zero gamma,

  --rw ← polynomial.degree_normalize p,


  --have v:(p * C (p.leading_coeff)⁻¹).monic,
  --exact polynomial.monic_mul_leading_coeff_inv w,
  --have z:p.degree=(p * C (p.leading_coeff)⁻¹).degree,
  --simp,
  --library_search,
  --let y:=polynomial.coe_norm_unit_of_ne_zero _ _, 

  
  --apply polynomial.degree_mod_by_monic_lt,

  
  --apply polynomial.degree_div_lt,
  --#check polynomial.degree_div_lt,

  sorry,

  
end

lemma module_map_bijective (h : p ≠ 0) : function.bijective (module_map p) :=
⟨module_map_injective p, module_map_surjective' p h⟩

def module_isomorphism (h : p ≠ 0) : polynomial.degree_lt F (p.nat_degree) ≃ₗ[F] adjoin_root p :=
{ .. (module_map p), .. equiv.of_bijective _ (module_map_bijective p h) }


def module_quotient_map : polynomial F →ₐ[F] adjoin_root p :=
{ to_fun := (adjoin_root.mk p).to_fun,
  map_zero' := (adjoin_root.mk p).map_zero,
  map_add' := (adjoin_root.mk p).map_add,
  map_one' := (adjoin_root.mk p).map_one,
  map_mul' := (adjoin_root.mk p).map_mul,
  commutes' := λ _, rfl, }

def canonical_basis: {n: ℕ| n<polynomial.nat_degree p }→ adjoin_root p:= λ (n:{n: ℕ| n<polynomial.nat_degree p }), adjoin_root.mk p (polynomial.X^(n:ℕ))

lemma canonical_basis_is_basis : is_basis F (canonical_basis p) :=
begin
  split,
  { apply linear_independent_iff.mpr,
    intros f hf,
    dsimp only [canonical_basis] at hf,
    dsimp only [finsupp.total] at hf,
    rw finsupp.lsum_apply at hf,
    dsimp [finsupp.sum] at hf,
    simp only [linear_map.id_coe, id.def] at hf,
    change f.support.sum (λ a, (f a) • (module_quotient_map p (X ^ ↑a))) = 0 at hf,
    simp only [←alg_hom.map_smul] at hf,
    haveI : is_add_monoid_hom (module_quotient_map p) := sorry,
    rw finset.sum_hom at hf,
    sorry,
     },
  { sorry, },
end


 




lemma adjunction_basis : is_basis F (canonical_basis p):=
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
      have decomp: (finsupp.total S (adjoin_root p) F η) l =
        (adjoin_root.mk p) ((finsupp.total ↥S (polynomial F) F ν) l),
      { rw comp,
        have is_fin':finset ↥S := finset.univ,
        symmetry,
        let algebra_1 :=algebra_map F (adjoin_root p),
        let algebra_2 :=algebra_map F (polynomial F),
        have adjoin_root_is_module_map:(adjoin_root.mk p).to_fun=(module_quotient_map p).to_fun:=by simpa,

        have eq_1:(adjoin_root.mk p) ((finsupp.total ↥S (polynomial F) F ν) l) = (module_quotient_map p)((finsupp.total ↥S (polynomial F) F ν) l):=
        by simpa[adjoin_root_is_module_map],

        have eq_2: (finsupp.total ↥S (adjoin_root p) F ((adjoin_root.mk p) ∘ ν)) l = (finsupp.total ↥S (adjoin_root p) F ((module_quotient_map p) ∘ ν)) l:=
        by simpa[adjoin_root_is_module_map],

        have eq_3: (module_quotient_map p)((finsupp.total ↥S (polynomial F) F ν) l) = (finsupp.total ↥S (adjoin_root p) F ((module_quotient_map p) ∘ ν)) l:=sorry,
        --dsimp[finsupp.total],
        --simp[finsupp.lmap_domain_total],
        --exact finsupp.lmap_domain_total F,
        --simp_rw[finsupp.lmap_domain_total],
        simp*,
        
        

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
linear_equiv.finite_dimensional (adjoin_root_equiv_fin_fun_degree p h)

lemma adjoin_root_findim_eq_degree (p : polynomial F) (h : p ≠ 0) :
  findim F (adjoin_root p) = nat_degree p :=
by {rw [← linear_equiv.findim_eq (adjoin_root_equiv_fin_fun_degree p h), findim_fin_fun]}

lemma adjoin_root_dim_eq_degree (p : polynomial F) (h : p ≠ 0) :
  dim F (adjoin_root p) = nat_degree p :=
by rw [← linear_equiv.dim_eq (adjoin_root_equiv_fin_fun_degree p h), dim_fin_fun]
