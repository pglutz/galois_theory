import field_theory.subfield
import ring_theory.algebra
import field_theory.minimal_polynomial
import linear_algebra.dimension
import linear_algebra.finite_dimensional

/- adjoining an element -/

--a little hacky (maybe there's a better way)
definition adjoin (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) : set E :=
field.closure (set.range (algebra_map F E) ∪ {α})

lemma adjoin_degree (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (α : E) (h : is_integral F α) :=
(finite_dimensional.findim F E) = (polynomial.degree (minimal_polynomial h))