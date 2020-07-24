import field_theory.subfield
import ring_theory.algebra

/- adjoining an element -/

--a little hacky (maybe there's a better way)
definition adjoin (F : Type*) [field F] (E : Type*) [field E] [h : algebra F E] (α : E) : set E :=
field.closure (set.range (algebra_map F E) ∪ {α})