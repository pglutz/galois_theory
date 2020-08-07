import primitive_element

lemma hmmm (F : Type*) [field F] (E : Type*) [field E] [algebra F E] (hs : is_separable F E) (hfd : finite_dimensional F E) : true :=
begin
    cases primitive_element F E hs hfd,
    sorry,
end