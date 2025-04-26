import Mathlib
import «RegularLocalRings».KrullsHeightTheorem
import «RegularLocalRings».EmbDim

local notation3:max "max" A => (IsLocalRing.maximalIdeal A)

variable {R : Type*} [CommRing R]

-- The Krull dimension of R cast as a natural number. If R has infinite Krull dimension or is the zero ring then
-- finRingKrullDim R = 0
noncomputable def finRingKrullDim (R : Type*) [CommRing R] : ℕ := ENat.toNat (WithBot.unbotD 0 (ringKrullDim R))

open Ideal

-- Instance that a noetherian local ring has finite Krull dimension. This follows from Krull's height
-- theorem
instance {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    FiniteRingKrullDim R := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr

  constructor
  have KDge0 := @ringKrullDim_nonneg_of_nontrivial R _ _
  by_contra hc
  rw[hc] at KDge0
  contradiction

  rw[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have finHeight := Ideal.height_le_spanFinrank (max R) Ideal.IsPrime.ne_top'
  have : Submodule.spanFinrank (max R) < (⊤ : ℕ∞) := ENat.coe_lt_top (Submodule.spanFinrank max R)

  by_contra hc
  have : (max R).height < ⊤ := lt_of_le_of_lt finHeight this
  have : (max R).height < (⊤ : WithBot ℕ∞) := WithBot.coe_lt_coe.mpr this
  rw[hc] at this
  contradiction


-- Coersion to help when coparing ringKrullDim and finRingKrullDim
lemma NatCast_WithBot_le (n m : ℕ) (h : (n : WithBot ℕ∞) ≤ m) : n ≤ m := by
  simp at h ⊢
  exact h


-- If R has finite Krull dimension then ringKrullDim R = finRingKrullDim R
theorem finRingKrullDim_ringKrullDim (R : Type*) [CommRing R] [FiniteRingKrullDim R] :
    ringKrullDim R = finRingKrullDim R := by
  have hn := (finiteRingKrullDim_iff_ne_bot_and_top.mp ‹_›).left
  have hm := (finiteRingKrullDim_iff_ne_bot_and_top.mp ‹_›).right

  let n : ℕ∞ := WithBot.unbot (ringKrullDim R) hn
  have h1 : ringKrullDim R = n := (WithBot.unbot_eq_iff hn).mp rfl
  have h3 : WithBot.unbotD 0 (ringKrullDim R) = (ringKrullDim R) := by
    rw[h1]
    rfl
  have : WithBot.unbotD 0 (ringKrullDim R) ≠ ⊤ := by
    by_contra hc
    obtain hl|hr := (@WithBot.unbotD_eq_iff ℕ∞ 0 ⊤ (ringKrullDim R)).mp hc
    exact hm hl
    exact hn hr.left

  have : ENat.toNat (WithBot.unbotD 0 (ringKrullDim R)) = WithBot.unbotD 0 (ringKrullDim R) := ENat.coe_toNat this
  unfold finRingKrullDim
  nth_rw 1 [← h3]
  nth_rw 1 [← this]
  rfl


theorem finRingKrullDim_mono (R : Type*) [CommRing R] [FiniteRingKrullDim R] (n : ℕ) :
    ringKrullDim R ≤ n ↔ finRingKrullDim R ≤ n := by
  rw[finRingKrullDim_ringKrullDim]
  exact Nat.cast_le


-- If I is prime and contained in a minimal prime p then I=p
lemma le_minimalPrimes
{R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {P : Ideal R} (hP : P ∈ minimalPrimes R) (hI : I ≤ P) :
    I = P := by
  rw[minimalPrimes_eq_minimals] at hP
  obtain ⟨hP1, hP2⟩ := hP
  have := hP2 ‹_› hI
  exact le_antisymm_iff.mpr ⟨hI, this⟩


-- If x is not contained in any minimal prime of R then the Krull Dim of R/x is strictly less
-- than the Krull Dim of R
-- This proof is modified from ringKrullDim_quotient_succ_le_of_nonZeroDivisor
lemma ringKrullDim_quotient_succ_le_of_not_in_minimalPrimes
{R : Type*} [CommRing R] {r : R} (hr : ∀ p ∈ minimalPrimes R, r ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := by
    let q := l.head.val
    have : (span {r} : Set R) ⊆ q.asIdeal := Subtype.coe_prop l.head

    refine lt_of_le_of_ne hp' ?_
    by_contra hc
    have : r ∈ (@Subtype.val (PrimeSpectrum R) (fun x ↦ x ∈ PrimeSpectrum.zeroLocus ↑(span {r})) (RelSeries.head l)).asIdeal := by
      have : r ∈ span {r} := mem_span_singleton_self r
      (expose_names; exact this_4 this)
    rw[← hc] at this
    exact hr p hp this
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp


-- If Dim R ≥ 1 then there is an element x of m that is not in any minimal prime of R.
-- This proof could be made more general and does not really require that R is local.
lemma IsLocalRing.one_le_ringKrullDim_element_notin_minimalPrimes
    [IsLocalRing R] [IsNoetherianRing R] (hKD : 1 ≤ ringKrullDim R) :
    ∃ x ∈ (max R), ∀ p ∈ minimalPrimes R, x ∉ p := by
  by_contra hc
  push_neg at hc

  let S := Set.Finite.toFinset (minimalPrimes.finite_of_isNoetherianRing R)
  have Sdef : (S : Set (Ideal R)) = minimalPrimes R := by
    exact Set.Finite.coe_toFinset (minimalPrimes.finite_of_isNoetherianRing R)

  have hp : ∀ i ∈ S, i ≠ ⊥ → i ≠ ⊥ → i.IsPrime := by
    intro i hi _ _
    have : i ∈ minimalPrimes R := by
      simp_all only [mem_maximalIdeal, mem_nonunits_iff, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, S]
    exact minimalPrimes_isPrime this

  have maxinmin : ∃ i ∈ S, (max R) ≤ i := by
    apply (@Ideal.subset_union_prime (Ideal R) R _ S id ⊥ ⊥ hp (max R)).mp
    intro x hx
    obtain ⟨p, hp1, hp2⟩ := hc x hx
    refine Set.mem_iUnion₂.mpr ?_
    use p
    have : p ∈ S := (Set.Finite.mem_toFinset (minimalPrimes.finite_of_isNoetherianRing R)).mpr hp1
    use this
    exact hp2

  obtain ⟨p , hp1, hp2⟩ := maxinmin
  have hp3 : p ∈ minimalPrimes R := by
    simp_all only [mem_maximalIdeal, mem_nonunits_iff, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, S]

  have maxp := le_antisymm_iff.mpr
    ⟨hp2 , IsLocalRing.le_maximalIdeal (IsPrime.ne_top (minimalPrimes_isPrime hp3))⟩

  rw[← maxp] at hp3

  have : Ring.KrullDimLE 0 R := by
    refine Ring.KrullDimLE.mk₀ ?_
    intro I hI
    have : I ≤ (max R) := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hI)
    have := le_minimalPrimes hp3 this
    exact (isMaximal_iff R).mpr this

  have : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp this

  rw[this] at hKD
  contradiction


theorem Min_Prime_over_ringKrullDim_Ind :
    ∀ (n : ℕ) (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], finRingKrullDim R = n → ∃ s : Finset R,
    s.card ≤ finRingKrullDim R ∧ (max R) ∈ (Ideal.span s).minimalPrimes := by
  intro N

  refine Nat.strong_induction_on N ?_
  intro n
  by_cases hn : n = 0

  intro _ R _ _ _ KD
  rw[hn] at KD
  have KD0 : ringKrullDim R = 0 := by
    rw[finRingKrullDim_ringKrullDim R]
    exact congrArg Nat.cast KD
  use ∅
  have : (∅ : Finset R).card = 0 := rfl
  rw[this]
  rw[KD]
  constructor
  exact Nat.zero_le 0
  have _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr KD0
  apply Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime.mpr
  simp only [Finset.coe_empty, span_empty, bot_le]

  intro ih R _ _ _ hKD
  push_neg at hn
  have : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
  have : finRingKrullDim R ≥ 1 := by simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
  have : ringKrullDim R ≥ 1 := by
    rw[finRingKrullDim_ringKrullDim]
    exact Nat.one_le_cast.mpr this

  obtain ⟨x, hx1, hx2⟩ := IsLocalRing.one_le_ringKrullDim_element_notin_minimalPrimes this

  have quotDim := ringKrullDim_quotient_succ_le_of_not_in_minimalPrimes hx2
  have _ : Nontrivial (R ⧸ (Ideal.span {x})) := Ideal.Quotient.nontrivial (Ideal.span_singleton_ne_top hx1)
  rw[finRingKrullDim_ringKrullDim R, finRingKrullDim_ringKrullDim (R ⧸ span {x})] at quotDim
  have : (finRingKrullDim (R ⧸ span {x})) + 1 ≤ (finRingKrullDim R) := by
    apply NatCast_WithBot_le
    exact quotDim

  have i : (finRingKrullDim (R ⧸ span {x})) < n := by linarith

  obtain ⟨s, hs1, hs2⟩ := ih (finRingKrullDim (R ⧸ span {x})) i (R ⧸ span {x}) rfl

  let q : (R ⧸ (Ideal.span {x})) ↪ R := {
    toFun := Quotient.out
    inj' := Quotient.out_injective
  }

  let S : Finset R := Finset.map q s
  have Scard : S.card = s.card := Finset.card_map q
  have hS' : (S ∪ {x} : Set R).Finite := Set.toFinite (↑S ∪ {x})
  have ncard := Set.ncard_union_le S {x}
  rw[Set.ncard_singleton x, Set.ncard_coe_Finset] at ncard
  let S' := Set.Finite.toFinset hS'

  have cardsle : S'.card ≤ S.card + 1 := by
    rw[← Set.ncard_coe_Finset]
    have : (S' : Set R).ncard = (S ∪ {x} : Set R).ncard := by
      rw[Set.Finite.coe_toFinset hS']
    linarith

  have im : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span S) = Ideal.span s := by
    have imS : (Ideal.Quotient.mk (Ideal.span {x}))'' S = s := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk, S, q]
      ext x_1 : 1
      simp_all only [Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and, Ideal.Quotient.mk_out, exists_eq_right]
    rw[Ideal.map_span, imS]

  have comapmap := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective (Ideal.span S)

  rw[im] at comapmap
  rw[Ideal.mk_ker] at comapmap
  have spanunion : Ideal.span (↑S ∪ {x}) = Ideal.span S ⊔ Ideal.span {x} := @Submodule.span_union R R _ _ _ S {x}

  have smspan : span S' = span (S ∪ {x}) := by simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk,
    Set.union_singleton, submodule_span_eq, Set.Finite.subset_toFinset, Set.subset_insert, Set.Finite.coe_toFinset, q,
    S, S']

  rw[spanunion, ← comapmap] at smspan

  have comapMinPrimes := @Ideal.comap_minimalPrimes_eq_of_surjective R (R ⧸ span {x}) _ _
    (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective (span s)

  rw[← smspan] at comapMinPrimes

  have maxmin : (max R) ∈ (span S').minimalPrimes := by
    have : (max R) = comap (Ideal.Quotient.mk (span {x})) (max (R ⧸ span {x})) := Eq.symm maxQuot
    have : (max R) ∈ comap (Ideal.Quotient.mk (span {x})) '' (span ↑s).minimalPrimes := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk, Set.union_singleton,
        Set.encard_singleton, Set.Finite.coe_toFinset, Set.mem_image, S', S, q]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [S', S, q]

    rw[← comapMinPrimes] at this
    exact this

  use S'
  refine ⟨?_, maxmin⟩
  linarith


-- There is an ideal generated by at most Dim R elements that m is minimal over.
-- In other words, there is an m primary ideal generated by Dim R elements.
theorem Min_Prime_over_ringKrullDim (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ s : Finset R, s.card ≤ finRingKrullDim R ∧ (max R) ∈ (Ideal.span s).minimalPrimes :=
  Min_Prime_over_ringKrullDim_Ind (finRingKrullDim R) R rfl


-- If x ∈ m then Dim R/x ≥ Dim R - 1. I.e. the dimension of the quotient drops by at most 1. Note that
-- this is not true non-local Noetherian rings in general
theorem IsLocalRing.Quotient_singleton_ringKrullDim [IsLocalRing R] [IsNoetherianRing R] (x : R)
[Nontrivial (R ⧸ (Ideal.span {x}))] : ringKrullDim R ≤ ringKrullDim (R ⧸ (Ideal.span {x})) + 1 := by

  obtain ⟨s , hs1 , hs2⟩ := Min_Prime_over_ringKrullDim (R ⧸ (Ideal.span {x}))

  let q : (R ⧸ (Ideal.span {x})) ↪ R := {
    toFun := Quotient.out
    inj' := Quotient.out_injective
  }

  let S : Finset R := Finset.map q s

  have Scard : S.card = s.card := Finset.card_map q
  have hS' : (S ∪ {x} : Set R).Finite := Set.toFinite (↑S ∪ {x})
  have ncard := Set.ncard_union_le S {x}
  rw[Set.ncard_singleton x, Set.ncard_coe_Finset] at ncard
  let S' := Set.Finite.toFinset hS'

  have cardsle : S'.card ≤ S.card + 1 := by
    rw[← Set.ncard_coe_Finset]
    have : (S' : Set R).ncard = (S ∪ {x} : Set R).ncard := by
      rw[Set.Finite.coe_toFinset hS']
    linarith

  have im : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span S) = Ideal.span s := by
    have imS : (Ideal.Quotient.mk (Ideal.span {x}))'' S = s := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk, S, q]
      ext x_1 : 1
      simp_all only [Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and, Ideal.Quotient.mk_out, exists_eq_right]
    rw[Ideal.map_span, imS]

  have comapmap := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective (Ideal.span S)

  rw[im] at comapmap
  rw[Ideal.mk_ker] at comapmap
  have spanunion : Ideal.span (↑S ∪ {x}) = Ideal.span S ⊔ Ideal.span {x} := @Submodule.span_union R R _ _ _ S {x}

  have smspan : span S' = span (S ∪ {x}) := by simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk,
    Set.union_singleton, submodule_span_eq, Set.Finite.subset_toFinset, Set.subset_insert, Set.Finite.coe_toFinset, q,
    S, S']

  rw[spanunion, ← comapmap] at smspan

  have comapMinPrimes := @Ideal.comap_minimalPrimes_eq_of_surjective R (R ⧸ span {x}) _ _
    (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective (span s)

  rw[← smspan] at comapMinPrimes

  have maxmin : (max R) ∈ (span S').minimalPrimes := by
    have : (max R) = comap (Ideal.Quotient.mk (span {x})) (max (R ⧸ span {x})) := Eq.symm maxQuot
    have : (max R) ∈ comap (Ideal.Quotient.mk (span {x})) '' (span ↑s).minimalPrimes := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk, Set.union_singleton,
        Set.encard_singleton, Set.Finite.coe_toFinset, Set.mem_image, S', S, q]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [S', S, q]

    rw[← comapMinPrimes] at this
    exact this

  have KDRle := (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes (span (S' : Set R)) (max R)) maxmin

  have maxKDR : (max R).height = ringKrullDim R := maximalIdeal_height_eq_ringKrullDim

  have spanrk := @Submodule.spanFinrank_span_le_ncard_of_finite R R _ _ _ S' (Finset.finite_toSet S')
  rw[Set.ncard_coe_Finset S'] at spanrk

  have g : (span (S' : Set R)).FG := by
    use S'

  rw[Submodule.fg_iff_spanRank_eq_spanFinrank.mpr g] at KDRle

  simp at KDRle

  have a := ENat.coe_le_coe.mpr spanrk

  have maxleK : (max R).height ≤ finRingKrullDim (R ⧸ span {x}) + 1 := by
    have a : (max R).height ≤ S'.card := Preorder.le_trans (max R).height (span (S' : Set R)).spanFinrank S'.card KDRle a
    have b : S'.card ≤ finRingKrullDim (R ⧸ span {x}) + 1 := by linarith
    have c : (S'.card : ℕ∞) ≤ finRingKrullDim (R ⧸ span {x}) + 1 := ENat.coe_le_coe.mpr b
    exact Preorder.le_trans (max R).height (↑S'.card) (↑(finRingKrullDim (R ⧸ span {x})) + 1) a c

  have al : ((max R).height : WithBot ℕ∞) ≤ finRingKrullDim (R ⧸ span {x}) + 1 := (WithBot.coe_le rfl).mpr maxleK

  rw[maxKDR, ← finRingKrullDim_ringKrullDim (R ⧸ span {x})] at al

  exact al


-- If x ∈ m \ m² then the minimal number of generators of m/x is the minimal number of generators for
-- m minus 1.
theorem IsLocalRing.Quotient_span_singleton_Submodule.spanFinrank
[IsLocalRing R] [IsNoetherianRing R] (x : R) [Nontrivial (R ⧸ (Ideal.span {x}))] (hx1 : x ∈ (max R)) (hx2 : x ∉ (max R)^2) :
    Submodule.spanFinrank (max (R ⧸ Ideal.span {x})) + 1 = Submodule.spanFinrank (max R) := by
  rw[← IsLocalRing.Embdim_eq_spanFinrank_maximal_ideal R, ← IsLocalRing.Embdim_eq_spanFinrank_maximal_ideal (R ⧸ Ideal.span {x})]
  exact Eq.symm (IsLocalRing.Embdim_Quotient_span_singleton hx1 hx2)


-- The minimal number of generators of m is an upper bound on the dimension of R
theorem IsLocalRing.ringKrullDim_le_spanFinrank (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Submodule.spanFinrank (max R) := by

  rw[← maximalIdeal_height_eq_ringKrullDim]
  have := Ideal.height_le_spanFinrank (max R) Ideal.IsPrime.ne_top'
  exact (WithBot.coe_le rfl).mpr this


-- If x is a non-unit non-zerodivisor then Dim R/x = Dim R - 1
theorem IsLocalRing.ringKrullDim_quotient_succ_eq_of_nonZeroDivisor
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {r : R} (hr : r ∈ nonZeroDivisors R) (hr' : ¬IsUnit r) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 = ringKrullDim R :=
  le_antisymm_iff.mpr ⟨ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr ,
  @IsLocalRing.Quotient_singleton_ringKrullDim R _ _ _ r
  (Ideal.Quotient.nontrivial (span_singleton_ne_top hr'))⟩
