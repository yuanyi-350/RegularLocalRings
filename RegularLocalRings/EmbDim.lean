import Mathlib

local notation3:max "max" A => (IsLocalRing.maximalIdeal A)

open IsLocalRing

-- This is proving that a (nontrivial) quotient of a local ring is a local ring
instance {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} [Nontrivial (R ⧸ I)] :
    IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

-- Ideal.Quotient.mk is the map from R to R/I
-- This theorem is saying that the preimage (Ideal.comap) of the maximal ideal in R/I is the maximal
-- ideal in R.
theorem maxQuot {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} [Nontrivial (R ⧸ I)] :
    Ideal.comap (Ideal.Quotient.mk I) (max (R ⧸ I)) = (max R) := by
  have : Ideal.IsMaximal (Ideal.comap (Ideal.Quotient.mk I) (max (R ⧸ I))) :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact IsLocalRing.eq_maximalIdeal this

-- This theorem is saying that the image (Ideal.map) of the maximal ideal in R is the maximal
-- ideal in R/I.
theorem maxQuot' {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} [Nontrivial (R ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (max R) = (max (R ⧸ I)) := by
  have := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (max (R ⧸ I))
  rw[maxQuot] at this
  exact this

-- The embedding dimension of a local ring defined to be the dimension of m/m^2
noncomputable def IsLocalRing.EmbDim (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : ℕ :=
    Module.finrank (ResidueField R) (CotangentSpace R)

-- This is essentially Nakayama's Lemma in the special case of a Local Ring
#check IsLocalRing.CotangentSpace.span_image_eq_top_iff

theorem IsLocalRing.Embdim_eq_spanFinrank_maximal_ideal (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.EmbDim R = (max R).spanFinrank := sorry

theorem IsLocalRing.Embdim_Quotient_span_singleton
{R : Type*} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[Nontrivial (R ⧸ Ideal.span {x})] (hx1 : x ∈ (max R)) (hx2 : x ∉ ((max R)^2)) :
    (IsLocalRing.EmbDim R) = IsLocalRing.EmbDim (R ⧸ Ideal.span {x}) + 1 := sorry
