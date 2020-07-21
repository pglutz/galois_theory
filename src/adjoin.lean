import field_theory.subfield
import ring_theory.algebra

variables (F : Type*) [field F] (K : Type*) [field K] [algebra F K]

--a little hacky (maybe there's a better way)
definition adjoin [field F] [field K] [algebra F K] (α : K) : set K := field.closure ((⊤ : set K) ∪ {α})