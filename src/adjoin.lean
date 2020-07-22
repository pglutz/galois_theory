import field_theory.subfield
import ring_theory.algebra

/- adjoining an element -/

--a little hacky (maybe there's a better way)
definition adjoin (F : Type*) [field F] (K : Type*) [field K] [h : algebra F K] (α : K) : set K :=
field.closure (set.range (algebra_map F K) ∪ {α})