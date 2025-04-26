import Mathlib
import «RegularLocalRings».LocalRingDimension


local notation3:max "max" A => (IsLocalRing.maximalIdeal A)

variable {R : Type*} [CommRing R]


-- Definition of a regular local ring. May change later to EmbDim R = ringKrullDim R once
-- EmbDim.lean is finished
class IsRegularLocalRing (R : Type*) [CommRing R] : Prop extends IsLocalRing R, IsNoetherianRing R where
  reg : (max R).spanFinrank = ringKrullDim R


-- If x ∈ m \ m² and R is regular, then R/x is regular. This is the most important fact
-- for inductively proving things about regular local rings
theorem IsRegularLocalRing.Quotient_span_singleton_IsRegularLocalRing
[hreg : IsRegularLocalRing R] (x : R) [Nontrivial (R ⧸ (Ideal.span {x}))] (hx1 : x ∈ (max R)) (hx2 : x ∉ (max R)^2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  apply IsRegularLocalRing.mk

  refine le_antisymm_iff.mpr ⟨?_, IsLocalRing.ringKrullDim_le_spanFinrank (R ⧸ Ideal.span {x})⟩

  have KDle := IsLocalRing.Quotient_singleton_ringKrullDim x
  have hh : ((Submodule.spanFinrank max R ⧸ Ideal.span {x}) + 1 : ℕ) ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    rw[IsLocalRing.Quotient_span_singleton_Submodule.spanFinrank x hx1 hx2]
    rw[hreg.reg]
    exact KDle

  have : ((Submodule.spanFinrank max R ⧸ Ideal.span {x}) + 1 : ℕ) = (((Submodule.spanFinrank max R ⧸ Ideal.span {x}) : WithBot ℕ∞) + 1) := rfl

  rw[this] at hh
  clear this
  rw[finRingKrullDim_ringKrullDim] at hh
  rw[finRingKrullDim_ringKrullDim]

  have natle :
  (Submodule.spanFinrank max R ⧸ Ideal.span {x}) + 1 ≤ (finRingKrullDim (R ⧸ Ideal.span {x})) + 1 :=
    NatCast_WithBot_le ((Submodule.spanFinrank max R ⧸ Ideal.span {x}) + 1) ((finRingKrullDim (R ⧸ Ideal.span {x})) + 1) hh

  have natle' : (Submodule.spanFinrank max R ⧸ Ideal.span {x}) ≤ (finRingKrullDim (R ⧸ Ideal.span {x})) := Nat.le_of_lt_succ natle

  exact Nat.cast_le.mpr natle'


-- Coersion for going between spanRank and spanFinrank for ideals in a noetherian ring.
lemma IsNoetherianRing.Ideal_spanRank_eq_spanFinrank [IsNoetherianRing R] (I : Ideal R) :
    I.spanRank = I.spanFinrank :=
  Submodule.fg_iff_spanRank_eq_spanFinrank.mpr ((isNoetherianRing_iff_ideal_fg R).mp ‹_› I)


-- A regular local ring of dimension 0 is a field.
lemma IsRegularLocalRing.ringKrullDim_zero_IsField
    (R : Type*) [CommRing R] [hR : IsRegularLocalRing R] (kd0 : ringKrullDim R = 0) :
    IsField R := by

  rw[← hR.reg] at kd0
  have hm : Submodule.spanFinrank (max R) = 0 := by simp_all only [Nat.cast_eq_zero]
  have SPzero : Submodule.spanRank (max R) = 0 := by
    rw[IsNoetherianRing.Ideal_spanRank_eq_spanFinrank (max R), hm]
    rfl
  have mBot := Submodule.spanRank_eq_zero_iff_eq_bot.mp SPzero
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr (id (mBot))


-- The key lemma in the proof that regular local rings are domains: If (x) is prime and
-- not minimal then R is a domain.
lemma IsLocalRing_IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain
{R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
(x : R) [hx : (Ideal.span {x}).IsPrime] (notMin : ¬Ideal.span {x} ∈ minimalPrimes R) :
    IsDomain R := by

  have zero_in_x : ⊥ ≤ Ideal.span {x} := bot_le
  have min_in_x := Ideal.exists_minimalPrimes_le zero_in_x
  obtain ⟨q , hq1, hq2⟩ := min_in_x

  have x_not_in_q : x ∉ q := by
    by_contra hx
    have : Ideal.span {x} ≤ q := (Ideal.span_singleton_le_iff_mem q).mpr hx
    have := le_antisymm_iff.mpr ⟨hq2, this⟩
    rw[this] at hq1
    exact notMin hq1

  have q_in_x_pow : ∀ n : ℕ, q ≤ Ideal.span {x}^n := by
    intro n
    induction n with
    | zero =>
      rw[Ideal.span_singleton_pow x 0]
      rw[pow_zero x]
      rw[Ideal.span_singleton_one]
      exact fun ⦃x⦄ a ↦ trivial

    | succ n ih =>
      intro y hy
      rw[Ideal.span_singleton_pow]
      rw[Ideal.span_singleton_pow] at ih
      obtain ⟨r , hr⟩ := Ideal.mem_span_singleton'.mp (ih hy)
      have qPrime : q.IsPrime := Ideal.minimalPrimes_isPrime hq1
      have xpow_not_q : x^n ∉ q := by
        by_contra hxp
        have := Ideal.IsPrime.mem_of_pow_mem qPrime n hxp
        contradiction

      rw[← hr] at hy
      have : r ∈ q := by
        have := Ideal.IsPrime.mem_or_mem qPrime hy
        subst hr
        simp_all only [bot_le, or_false]

      obtain ⟨a , ha⟩ := Ideal.mem_span_singleton'.mp (hq2 this)
      apply Ideal.mem_span_singleton'.mpr
      rw[← ha] at hr
      use a
      rw[← hr]
      ring

  have x_not_top : Ideal.span {x} ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›

  have KIT := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {x}) ‹_›

  have qZero : q ≤ ⊥ := by
    intro y hy
    have hyx : ∀(n : ℕ), y ∈ Ideal.span {x} ^ n := by
      intro n
      exact q_in_x_pow n hy

    have := Ideal.mem_iInf.mpr hyx
    rw[KIT] at this
    assumption

  have qeqZero : q = ⊥ := (Submodule.eq_bot_iff q).mpr qZero
  have qPrime : q.IsPrime := Ideal.minimalPrimes_isPrime hq1
  rw[qeqZero] at qPrime
  exact IsDomain.of_bot_isPrime R


-- The induction used to show that regular local rings are domains.
theorem IsRegularLocalRing_IsDomain_Induction :
    ∀(n : ℕ) (R : Type*) [CommRing R] [IsRegularLocalRing R] (_ : Submodule.spanFinrank (max R) = n), IsDomain R := by
  intro n

  -- We do induction on the dimeinsion of R
  induction n with
  | zero =>
    intro R _ hR hm
    have : ringKrullDim R = 0 := by
      rw[← hR.reg]
      simp only [Nat.cast_eq_zero]
      exact hm
    let FS : Field R := IsField.toField (IsRegularLocalRing.ringKrullDim_zero_IsField R this)
    exact Field.isDomain

  | succ n ih =>
    intro R _ hR hn
    by_contra hR_not_Dom

    -- Our goal is to show that max R is the union of (max R)^2 along with the minimal primes of R.
    have isMinPrime : ∀(x : R), (x ∈ max R) → (x ∉ (max R)^2) → (Ideal.span {x} ∈ minimalPrimes R) := by
      intro x hx hx2

      have xPrime : (Ideal.span {x}).IsPrime := by
        apply (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp

        have _ : Nontrivial (R ⧸ (Ideal.span {x})) := Ideal.Quotient.nontrivial (Ideal.span_singleton_ne_top hx)


        have minGenquot : Submodule.spanFinrank (max (R ⧸ (Ideal.span {x}))) = n := by
          have := IsLocalRing.Quotient_span_singleton_Submodule.spanFinrank x hx hx2
          simp_all only [Nat.add_left_inj]

        have quotReg : IsRegularLocalRing (R ⧸ (Ideal.span {x})) := IsRegularLocalRing.Quotient_span_singleton_IsRegularLocalRing x hx hx2

        exact ih (R ⧸ (Ideal.span {x})) minGenquot

      by_contra hx3

      exact hR_not_Dom (IsLocalRing_IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain x hx3)

    clear ih

    let S' := (minimalPrimes R) ∪ {(max R)^2}
    have sFin : S'.Finite := Set.Finite.union (minimalPrimes.finite_of_isNoetherianRing R) (Set.finite_singleton ((max R) ^ 2))

    let S := Set.Finite.toFinset sFin

    have hp : (∀ i ∈ S, (i ≠ (max R)^2) → (i ≠ (max R)^2) → i.IsPrime) := by
      intro I hI hm1 _
      have : I ∈ S' := (Set.Finite.mem_toFinset sFin).mp hI
      obtain h1|h2 := this
      exact Ideal.minimalPrimes_isPrime h1
      contradiction

    have maxinmin : ∃ i ∈ S, (max R) ≤ i := by
      apply (@Ideal.subset_union_prime (Ideal R) R _ S (λ x => x) ((max R)^2) ((max R)^2) hp (max R)).mp
      intro x hx
      obtain xinm2|xnotinm2 := Classical.em (x ∈ (max R) ^ 2)
      refine Set.mem_iUnion₂.mpr ?_
      use ((max R)^2)
      use (Set.Finite.mem_toFinset sFin).mpr (Set.mem_union_right (minimalPrimes R) rfl)
      exact xinm2
      have xminP := isMinPrime x hx xnotinm2
      refine Set.mem_iUnion₂.mpr ?_
      use Ideal.span {x}
      use (Set.Finite.mem_toFinset sFin).mpr (Set.mem_union_left {(max R) ^ 2} (isMinPrime x hx xnotinm2))
      exact Ideal.mem_span_singleton_self x


    obtain ⟨P, hP1, hP2⟩ := maxinmin

    have dimNotZero : ringKrullDim R ≠ 0 := by
      rw[← hR.reg, hn]
      have : n+1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      exact Nat.cast_ne_zero.mpr this

    apply dimNotZero

    clear hn hR_not_Dom isMinPrime dimNotZero hp

    obtain h1|h2 := (Set.Finite.mem_toFinset sFin).mp hP1

    clear hP1 S sFin S'

    rw[← ringKrullDimZero_iff_ringKrullDim_eq_zero]
    refine Ring.KrullDimLE.mk₀ ?_
    intro I hI
    have : I ≤ (max R) := by exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hI)
    have : I ≤ P := by exact fun ⦃x⦄ a ↦ hP2 (this a)
    have IP := le_minimalPrimes ‹_› this
    have mP := le_minimalPrimes ‹_› hP2
    have Im : I = (max R) := by
      rw[IP, mP]
    rw[Im]
    exact IsLocalRing.maximalIdeal.isMaximal R

    have hm : (max R) ≤ (max R)^2 := by
      simp_all only [Set.union_singleton, Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, S, S']

    have _ : IsNoetherianRing R := by infer_instance

    have mFG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› (max R)
    have mlem2 : (max R) ≤ (max R) • (max R) := by
      have : (max R) • (max R) = (max R) * (max R) := rfl
      rw[this, Eq.symm (pow_two max R)]
      exact hm

    have mlejac : (max R) ≤ Ideal.jacobson ⊥ := by
      have : (⊥ : Ideal R) ≠ ⊤ := bot_ne_top
      rw[IsLocalRing.jacobson_eq_maximalIdeal ⊥ this]

    have mbot := @Submodule.eq_bot_of_le_smul_of_le_jacobson_bot R R _ _ _ (max R) (max R) mFG mlem2 mlejac

    exact ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr mbot)


-- Regular local rings are domains
theorem IsRegularLocalRing_IsDomain
{R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  exact IsRegularLocalRing_IsDomain_Induction (Submodule.spanFinrank (max R)) R rfl



/-
#check Ideal.exists_minimalPrimes_le
#check Ideal.iInf_pow_eq_bot_of_localRing
#check minimalPrimes.finite_of_isNoetherianRing
#check Ideal.subset_union_prime
#check Ideal.map_isPrime_of_surjective
#check Ideal.map_eq_iff_sup_ker_eq_of_surjective
#check Ideal.comap_map_of_surjective'
#check Ideal.mk_ker
#check Ideal.Quotient.mk_surjective
#check Ideal.comap_injective_of_surjective
#check Ideal.map_surjective_of_surjective
#check IsLocalRing.of_surjective
-/
