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

--open Submodule
open Cardinal -- allows us to write `#s` instead of `Cardinal.mk s`

--Lemma: if σ : M → N is an injective R-module map and p ⊆ M is a submodule, then spanRank(σ(p)) ≤ spanRank(p).
lemma Submodule.spanRank_inj_map_le.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    (map σ p).spanRank ≤ p.spanRank := by
  obtain ⟨s, hs1, hs2⟩ := Submodule.exists_span_set_card_eq_spanRank p
  let s' : Set N := σ '' s
  have : #s = #s' := Eq.symm (mk_image_eq hσ)
  have a := Submodule.map_span σ s
  rw[hs2] at a
  rw[← hs1]
  have b := @Submodule.spanRank_span_le_card R N _ _ _ s'
  rw[← a] at b
  rw[this]
  exact b

--Lemma: if σ : M → N is an injective R-module map and p ⊆ M is a submodule, then spanRank(p) ≤ spanRank(σ(p)).
lemma Submodule.spanRank_inj_map_le'.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    p.spanRank ≤ (map σ p).spanRank := by
  obtain ⟨s, hs1, hs2⟩ := Submodule.exists_span_set_card_eq_spanRank (map σ p)
  let s' : Set M := σ⁻¹' s
  have hss' : σ '' s' = s := by
    ext x
    constructor
    . rintro ⟨a, ⟨ha1, ha2⟩ ⟩
      rw [← ha2]
      exact ha1
    . intro hx
      have a : x ∈ span R s := by exact mem_span.mpr fun p a ↦ a hx
      rw[hs2] at a
      obtain ⟨y, hy1, hy2⟩ := Submodule.mem_map.mp a
      have : y ∈ s' := by
        refine Set.mem_preimage.mpr ?_
        rw[hy2]
        exact hx
      use y

  have s's : #s' = #s := by
    rw[← hss']
    exact Eq.symm (mk_image_eq hσ)
  have b := @Submodule.spanRank_span_le_card R M _ _ _ s'
  have a := Submodule.map_span σ s'
  rw[hss', hs2] at a
  rw[Submodule.map_injective_of_injective hσ a] at b
  rw[s's, hs1] at b
  exact b

--Lemma: if σ : M → N is an injective R-module map and p ⊆ M is a submodule, then spanRank(p) = spanRank(σ(p)).
lemma Submodule.spanRank_inj_map.{u} {R : Type*} [CommRing R] {M : Type u} {N : Type u}
[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (σ : M →ₗ[R] N) (p : Submodule R M)
(hσ : Function.Injective σ) :
    p.spanRank = (map σ p).spanRank :=
  le_antisymm_iff.mpr ⟨Submodule.spanRank_inj_map_le' σ p hσ, Submodule.spanRank_inj_map_le σ p hσ⟩

--Lemma: if M is an R-module and N ⊆ M is an R-submodule, then spanRank(N) = spanRank(⊤ : Submodule R N).  That is, the span rank of N as a submodule of M is the same as the span rank of N as a submodule of itself.
lemma SpanRankOfSubmodule_eq_spanFinrankOfTop {R : Type*} [CommRing R] {M : Type*}
[AddCommGroup M] [Module R M] (N : Submodule R M) :
    Submodule.spanRank N = (⊤ : Submodule R N).spanRank := by
  have h1 := Submodule.map_subtype_top N
  have h2 := Submodule.spanRank_inj_map N.subtype (⊤ : Submodule R N) (Submodule.injective_subtype N)
  rw[h2]
  rw[h1]

--Lemma: If R is a noetherian ring, M is a finite R-module, and N ⊆ M is an R-submodule, then spanFinRank(N) = spanFinRank(⊤ : Submodule R N).  That is, the spanFinrank of N as a submodule of M is the same as the spanFinrank of N as a submodule of itself.
lemma SpanFinRankOfSubmodule_eq_spanFinrankOfTop (R : Type*) [CommRing R] [IsNoetherianRing R] (M : Type*)
[AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
  Submodule.spanFinrank N = (⊤ : Submodule R N).spanFinrank := by
  have N_fg : N.FG := IsNoetherian.noetherian N
  have top_fg : (⊤ : Submodule R N).FG := IsNoetherian.noetherian ⊤
  have h_spanRank : N.spanRank = (⊤ : Submodule R N).spanRank := SpanRankOfSubmodule_eq_spanFinrankOfTop N
  have N_spanRank_eq_spanFinrank : N.spanRank = N.spanFinrank := Submodule.fg_iff_spanRank_eq_spanFinrank.mpr N_fg
  have top_spanRank_eq_spanFinrank : (⊤ : Submodule R N).spanRank = (⊤ : Submodule R N).spanFinrank := Submodule.fg_iff_spanRank_eq_spanFinrank.mpr top_fg
  rw [N_spanRank_eq_spanFinrank,top_spanRank_eq_spanFinrank] at h_spanRank
  exact Nat.cast_injective h_spanRank




--Lemma: For a finite dimensional vector space over a field, finrank(V) = spanFinrank(V)
lemma Finrank_eq_spanFinrankOfTop (k : Type*) [Field k]  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] : Module.finrank k V = (⊤ : Submodule k V).spanFinrank := by
  --rank(V) = spanRank(V)
  have rank_eq_spanRank : Module.rank k V = (⊤ : Submodule k V).spanRank := Submodule.rank_eq_spanRank_of_free
  --spanRank(V) = spanFinrank(V)
  have spanrank_eq_spanFinrank :  (⊤ : Submodule k V).spanRank =  (⊤ : Submodule k V).spanFinrank := by
    have top_fg : (⊤ : Submodule k V).FG := IsNoetherian.noetherian (⊤ : Submodule k V)
    exact Submodule.fg_iff_spanRank_eq_spanFinrank.mpr top_fg
  --finrank(V) = rank(V)
  have finrank_eq_rank : Module.finrank k V = Module.rank k V := Module.finrank_eq_rank k V
  --now use finrank(V) = rank(V) = spanRank(V) = spanFinrank(V)
  rw [rank_eq_spanRank, spanrank_eq_spanFinrank, Nat.cast_inj] at finrank_eq_rank
  exact finrank_eq_rank

--Theorem: For a noetherian local ring (R,m), spanFinrank(m) = dim m/m^2
--To do: prove a more general version of Nakayama's lemma for a finitely graded module M over a noetherian local ring (r,m): spanFinrank(M) = dim M/mM, where spanFinrank(M):=spanFinrank(⊤: Submodule R M)
theorem IsLocalRing.Embdim_eq_spanFinrank_maximal_ideal (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.EmbDim R = (max R).spanFinrank := by
  rw [Nat.eq_iff_le_and_ge]
  constructor
  . -- easier direction: finrank(m/m^2) ≤ spanFinrank(m)
    --obtain generators of m such that #generators = finrank(m/m^2)
    have h1 : ∃ s : Set (max R), s.encard = ↑(Submodule.spanFinrank max R) ∧ Submodule.span R s = ⊤ := by
      --this is proved almost entirely using
      --Submodule.FG.exists_span_set_encard_eq_spanFinrank
      --but annoyingly this returns a subset of R, rather than m
      have m_fg : (max R).FG := IsNoetherian.noetherian (max R)
      apply Submodule.FG.exists_span_set_encard_eq_spanFinrank at m_fg
      obtain ⟨s, hs1, hs2⟩ := m_fg
      have hs3 : s ⊆  (max R) := by
        rw [← Submodule.span_le, hs2]
      --let inc := fun (x : max R) => (x : R)
      let inc := (max R).subtype
      let s' : Set (max R) := inc⁻¹' s
      have hs' : (inc '' s') = s := by aesop
      use s'
      have inc_injective : Function.Injective inc := Subtype.val_injective
      have card_s_eq_card_s' := Function.Injective.encard_image inc_injective s'
      rw [hs'] at card_s_eq_card_s'
      constructor
      . --s'.encard = ↑(Submodule.spanFinrank max R)
        rw [← card_s_eq_card_s']
        exact hs1
      . --Submodule.span R s' = ⊤
        have hsp := Submodule.map_span inc s'
        rw[hs', hs2] at hsp
        have mptop := Submodule.map_subtype_top (max R)
        have inj := Submodule.map_injective_of_injective inc_injective
        have : Submodule.map inc (Submodule.span R s') = Submodule.map inc ⊤ := by
          rw[hsp, mptop]
        exact inj this
    --let m_gens be a set generators of m such that #m_gens = spanFinrank(m)
    --Strategy: (1) show that im_m_gens := image of m_gens under m -> m/m^2 is a generating set
    --          (2) show that dim(m/m^3) ≤ #im_m_gens = #m_gens = spanFinrank(m)
    obtain ⟨m_gens, m_gens_card, hm_gens_span⟩ := h1
    have m_gens_finite : m_gens.Finite := Set.finite_of_encard_eq_coe m_gens_card
    have m_gens_card2 : m_gens.ncard = (max R).spanFinrank := by
      rw [← (Set.Finite.cast_ncard_eq m_gens_finite)] at m_gens_card
      exact Eq.symm ((fun {a b} ↦ ENat.coe_inj.mp) (id (Eq.symm m_gens_card)))
    rw [← m_gens_card2]
    rw [EmbDim]
    let im_m_gens := ⇑(max R).toCotangent '' m_gens
    let subspace := Submodule.span (ResidueField R) im_m_gens
    have hm_gens_cot_span : subspace = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr hm_gens_span
    have h1 : im_m_gens.ncard ≤ m_gens.ncard := by
      exact Set.ncard_image_le m_gens_finite
    have h2 : im_m_gens.Finite := Set.Finite.image (⇑(max R).toCotangent) m_gens_finite
    have h3 : subspace.spanFinrank ≤ im_m_gens.ncard := Submodule.spanFinrank_span_le_ncard_of_finite h2
    have h4 : subspace.spanFinrank ≤ m_gens.ncard := Nat.le_trans h3 h1
    clear h1 h3
    have h5 : subspace.spanRank  = Module.rank (ResidueField R) (CotangentSpace R) := by
      rw [hm_gens_cot_span]
      have : StrongRankCondition R := by
        exact strongRankCondition_of_orzechProperty R
      have : Module.Free (ResidueField R) (CotangentSpace R) := by
        exact Module.Free.of_divisionRing (ResidueField R) (CotangentSpace R)
      exact Eq.symm Submodule.rank_eq_spanRank_of_free
    rw [← Module.finrank_eq_rank (ResidueField R) (CotangentSpace R)] at h5
    have subspace_fg : subspace.FG := by
      exact IsNoetherian.noetherian subspace
    rw [← @Submodule.fg_iff_spanRank_eq_spanFinrank (ResidueField R) (CotangentSpace R) _ _ _ subspace] at subspace_fg
    rw [subspace_fg] at h5
    have h6 : subspace.spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) := by
      exact Nat.cast_inj.mp h5
    rw [← h6]
    exact h4
  . --harder direction: finrank(m/m^2) ≥ spanFinrank(m)
    unfold EmbDim
    let res := ResidueField R
    let cot := CotangentSpace R
    have cot_fg : Module.Finite res cot := instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing R
    have cot_fg' : (⊤ : Submodule res cot).FG := by
      exact IsNoetherian.noetherian (⊤ : Submodule res cot)
    obtain ⟨s, s_card, s_span⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank cot_fg'
    have s_finite : s.Finite := Set.finite_of_encard_eq_coe s_card
    let p := ⇑(max R).toCotangent
    have p_surj : Function.Surjective p := Ideal.toCotangent_surjective max R
    let p_has_right_inv := p_surj.hasRightInverse
    cases' p_has_right_inv with p_inv hp_inv
    clear p_surj p_has_right_inv
    change cot → ↥max R at p_inv
    let sinv := p_inv '' s
    have im_of_sinv_eq_s : (p '' sinv) = s := Function.LeftInverse.image_image hp_inv s
    have nakayama : Submodule.span (ResidueField R) (⇑(max R).toCotangent '' sinv) = ⊤ ↔ Submodule.span R sinv = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff
    rw [im_of_sinv_eq_s] at nakayama
    --#sinv ≤ #s
    have inequality2 : sinv.ncard ≤ s.ncard := Set.ncard_image_le s_finite
    rw [nakayama] at s_span
    have sinv_finite : sinv.Finite := Set.Finite.image p_inv s_finite

    --Determine the rank of the span of sinv
    have h_span_of_sinv : (Submodule.span R sinv).spanFinrank ≤ sinv.ncard := Submodule.spanFinrank_span_le_ncard_of_finite sinv_finite
    have top_fg : (⊤ : Submodule res cot).FG := IsNoetherian.noetherian (⊤ : Submodule res cot)
    --we can now conclude: ⊤.spanFinrank ≤ sinv.ncard
    rw [s_span] at h_span_of_sinv

    --Sketch: spanFinrank(m) ≤(1) sinv.ncard ≤(2) s.ncard =(3) finrank(m/m^2)
    have inequality1 : (Submodule.spanFinrank max R) ≤ sinv.ncard := by
      --this should follow from s_spna : span s_inv = m
      have h1 := (@Submodule.spanFinrank_span_le_ncard_of_finite R (max R) _ _ _ sinv) sinv_finite
      have h2 : (Submodule.span R sinv).spanFinrank = (Submodule.spanFinrank max R) := by
        rw [s_span]
        rw [← SpanFinRankOfSubmodule_eq_spanFinrankOfTop]
      linarith

    have equality3 : s.ncard = Module.finrank res cot := by
      have finrank_eq_SpanFinrank_of_top : Module.finrank res cot = (⊤ : Submodule res cot).spanFinrank := by
        rw [Finrank_eq_spanFinrankOfTop]
      rw [finrank_eq_SpanFinrank_of_top]
      have h6 : s.ncard = s.encard := Set.Finite.cast_ncard_eq s_finite
      rw [← h6] at s_card
      have s_card' : s.ncard = (⊤ : Submodule res cot).spanFinrank := Eq.symm ((fun {a b} ↦ ENat.coe_inj.mp) (id (Eq.symm s_card)))
      exact s_card'

    linarith

theorem dimQuotientSpanSingle_eq_oneless {k : Type*} [Field k]  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (x : V)
 (hx : x ≠ 0) : Module.finrank k V = (Module.finrank k (V ⧸ (Submodule.span k {x}))) + 1 := by
  let S := Submodule.span k {x}
  have hS : Module.finrank k S = 1 := finrank_span_singleton hx
  --use rank-nullity: dim V = dim (V/S) + dim S
  have rank_nullity : Module.finrank k V = Module.finrank k (V ⧸ S) + Module.finrank k S := (Submodule.finrank_quotient_add_finrank S).symm
  rw [hS] at rank_nullity
  exact rank_nullity

theorem IsLocalRing.Embdim_Quotient_span_singleton
{R : Type*} {x : R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
[Nontrivial (R ⧸ Ideal.span {x})] (hx1 : x ∈ (max R)) (hx2 : x ∉ ((max R)^2)) :
    (IsLocalRing.EmbDim R) = IsLocalRing.EmbDim (R ⧸ Ideal.span {x}) + 1 := by
  let k := ResidueField R
  let V := CotangentSpace R
  let p := ⇑(max R).toCotangent
  let x' := p ⟨x, hx1⟩
  have hx' : x' ≠ 0 := by
    sorry
  have hdim : Module.finrank k V = (Module.finrank k (V ⧸ (Submodule.span k {x'}))) + 1 := dimQuotientSpanSingle_eq_oneless x' hx'
  let Rmodx := R ⧸ Ideal.span {x}
  let cot_Rmodx := CotangentSpace Rmodx
  have h : cot_Rmodx ≃ (CotangentSpace R) ⧸ (Submodule.span (ResidueField R) {x'})  := by
    sorry
  repeat rw [EmbDim]
  have h_iso_residue_fields : ResidueField (R ⧸ Ideal.span {x}) ≃ k := by
    sorry
  sorry

variable (R : Type*) [CommRing R] (N : Type*) [AddCommMonoid N] [Module R N] (M : Submodule R N)  (x : M)

#check x
#check M.subtype x
#check Function.Embedding.subtype
#check M.subtype

#check (Submodule.MapSubtype.relIso M).toFun ⊤
