import ring_theory.algebra
import field_theory.minimal_polynomial
import field_theory.separable
import adjoin

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

instance subfield_subset_subfield_algebra (J K : set E) [is_subfield J] [is_subfield K] (h : J ⊆ K) : algebra J K := {
    to_fun := λ x, ⟨↑x,begin
        cases x with x hx,
        exact h hx,
    end⟩,
    smul := λ x y, ⟨↑x,begin
        cases x with x hx,
        exact h hx,
    end⟩ * y,
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl,
    commutes' := λ x y, mul_comm _ _,
    smul_def' := λ x y, rfl,
}

instance subfield_subset_subfield_scalar (J K : set E) [is_subfield J] [is_subfield K] (h : J ⊆ K) :
has_scalar J K := {
    smul := λ x y, ⟨↑x,begin
        cases x with x hx,
        exact h hx,
    end⟩ * y,
}

instance subfield_subset_subfield_scalar_tower (J K : set E) [is_subfield J] [is_subfield K] (h : J ⊆ K) :
@is_scalar_tower J K E (subfield_subset_subfield_scalar J K h) _ _ := {
    smul_assoc :=
    begin
        intros x y z,
        change ↑(_ * y) * z = x * (y * z),
        rw ←mul_assoc,
        refl,
    end,
}

lemma subfield_composition (J K : set E) [is_subfield J] [is_subfield K] (h : J ⊆ K) :
(algebra_map K E).comp(@algebra_map J K _ _ (subfield_subset_subfield_algebra J K h)) = algebra_map J E :=
begin
    ext,
    refl,
end

lemma separable.subfield_aux (J K : set E) [is_subfield J] [is_subfield K] (h : J ⊆ K) (h_sep : is_separable J E) : is_separable K E :=
begin
    intro x,
    cases h_sep x with hx hs,
    have key := @is_integral_of_is_scalar_tower J K E _ _ _ (subfield_subset_subfield_algebra _ _ h) _ _ _ x hx,
    use key,
    set f := @algebra_map J K _ _ (subfield_subset_subfield_algebra J K h),
    set p := (minimal_polynomial hx).map f,
    have key' : (minimal_polynomial key) ∣ p,
    apply minimal_polynomial.dvd,
    dsimp[polynomial.aeval],
    rw polynomial.eval₂_map,
    rw subfield_composition J K h,
    apply minimal_polynomial.aeval,
    cases key' with q hq,
    have hp : p.separable := polynomial.separable.map hs,
    rw hq at hp,
    exact polynomial.separable.of_mul_left hp,
end

lemma separable.subfield (K : set E) [is_subfield K] (F_sep : is_separable F E) (h : set.range (algebra_map F E) ⊆ K) : is_separable K E :=
separable.subfield_aux (set.range (algebra_map F E)) K h (inclusion.separable F_sep)

lemma adjoin_is_separable (F_sep : is_separable F E) (S : set E) : is_separable (adjoin F S) E :=
separable.subfield F (adjoin F S) F_sep (field_subset_adjoin F S)

lemma adjoin_simple_is_separable (F_sep : is_separable F E) (α : E) : is_separable (F[α]) E :=
adjoin_is_separable F F_sep {α}