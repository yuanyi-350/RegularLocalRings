-- This module serves as the root of the `RegularLocalRings` library.
-- Import modules here that should be built as part of the library.
import «RegularLocalRings».Basic
--test
import Mathlib
open IsLocalRing

--let's create convenient notation for a local ring
--max A = maximal ideal of A
--res A = residue field of A
--cotan A = cotangent space m/m^2 as a vector space over res A
local notation3:max "max" A => (maximalIdeal A)
local notation3:max "res" A => (ResidueField A)
local notation3:max "cotan" A => (CotangentSpace A)

----------------------------------------------------------------------------
--let's check if the notation works
variable (A : Type) [hCR : CommRing A] [hLR : IsLocalRing A]
#check max A
#check res A
#check cotan A

--let's verify that res A is a field
example : IsField res A := by
  exact Semifield.toIsField res A

--If A is noetherian, then cotan A is a finite module over res A
example (hNoeth : IsNoetherianRing A) : Module.Finite (res A) (cotan A) := by
  exact instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing A
--or equivalently a finite dimensional vector space over res A
example (hNoeth : IsNoetherianRing A) : FiniteDimensional (res A) (cotan A) := by
  exact instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing A
----------------------------------------------------------------------------


----------------------------------------------------------------------------
--Properties of local noetherian rings

/-noetherian local rings have finite dimension
this doesn't seem to be in mathlib and should be an easy consequence of
Krull's principal ideal theorem-/
theorem noetherianLocalRings_have_finiteDimension (R : Type) [hCR : CommRing R] [hLR : IsLocalRing R] (hNoeth : IsNoetherianRing R) : ringKrullDim R < ⊤    := by
  sorry
--We could then use ENat.coe_toNat to get that ringKrullDim A ∈ ℕ

def FinGenSetsCards {R : Type*} [CommRing R] (I : Ideal R) : Set ℕ := {n : ℕ | ∃(s : Finset R), Ideal.span s = I ∧ (n = s.card)}

noncomputable def minGenerators {R : Type*} [CommRing R] (I : Ideal R) : ℕ :=
    sInf (FinGenSetsCards I)
--Jarod: What does this return if FinGenSetsCards is empty, i.e., if I is
--not finitely generated.  Is it zero?

--In a noetherian local ring, the minimal number of generators = dim m/m^2
theorem minGenerators_eq_dimCotangentSpace {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]  : minGenerators (max R) = Module.finrank (ResidueField R) (CotangentSpace R) := by
--Informal proof:  Nakayama
  sorry


----------------------------------------------------------------------------


----------------------------------------------------------------------------
--Regular local rings

--A regular local ring is a noetherian local ring R with  dim m/m^2 = dim R
def IsRegularLocalRing (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R
--By minGenerators_eq_dimCotangentSpace, this definition is equivalent to
--requiring minGenerators (max R) = ringKrullDim R


----------------------------------------------------------------------------
--Example: Can we check that k[x_1, ..., x_n]_{(x_1, ..., x_n)} and
--k[[x_1, ..., x_n]] are regular local rings?
----------------------------------------------------------------------------

/-Main goal: A regular local ring R is a domain.
This is theorem IsRegularLocalRing_IsDomain below
Informal proof (Eisenbud Cor 10.14):  Proof by induction on dim R.
•Base case dim R = 0: dim m/m^2 = 0, so m = 0, so R is a field, hence a domain.
•Inductive step: Assume dim R = d > 0. By Nakayama's lemma, we have that
m^2 ≠ m, so by prime avoidance and the finiteness of the set of minimal primes
of R, we may find an element x ∈ m that is not contained in m^2 nor contained in
any of the minimal primes of R.
-Set S = R/x and n = mS be its maximal ideal. By the choice of x, dim S < dim R,
hence dim S = d-1 by Krull's principal ideal theorem.  Since n/n^2 = m/(m^2 + (x)),
dim n/n^2 ≤ d-1.  Hence dim n/n^2 ≤ d-1, which is enough to conclude that S is
regular. By the inductive hypothesis, S is a domain.  The proof now follows from
the following claim.

Claim: If R is a noetherian local ring and x ∈ R such that (x) is a prime ideal
that is not minimal, then R is a domain.
Pf of claim: There exists a minimal prime q ⊊ (x).  We will show that mq = q,
hence q = 0 by Nakayama's lemma. For y ∈ q, we can write y = ax for a ∈ R.
Since x ∉ q and q is prime, a ∈ q.  This shows that (x)q=q, hence mq=q.
Since q = 0 is prime, R is an integral domain.
-/

--Lemma: If (R, m) is a noetherian local ring and # minGenerators = 0, then R is
--a domain.
-- This is the base case of the induction.
lemma IsRegularLocalRing_IsDomain_Dim_zero
(R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hm : minGenerators (max R) = 0) :
    IsDomain R := by
  unfold minGenerators at hm
  rw[Nat.sInf_eq_zero] at hm
  obtain h1|h2 := hm
  {
    unfold FinGenSetsCards at h1
    obtain ⟨s , hs⟩ := h1
    obtain ⟨hsl , hsr⟩ := hs
    have semp : s = ∅ := Finset.card_eq_zero.mp (Eq.symm hsr)
    rw[semp] at hsl
    have empspnzero : Ideal.span (∅ : Finset R) = (⊥ : Ideal R) := by
      rw[Finset.coe_empty]
      exact Ideal.span_empty
    rw[empspnzero] at hsl
    have : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr (id (Eq.symm hsl))
    let FS : Field R := IsField.toField this
    exact Field.isDomain
  }
  have maxFG : (max R).FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› max R
  obtain ⟨s , hs⟩ := maxFG
  have : s.card ∈ FinGenSetsCards (max R) := by
    use s
  rw[h2] at this
  contradiction

--Key Lemma: If R is a noetherian local ring and (x) is a prime ideal that is not minimal,
--R is a domain.
lemma IsLocalRing_IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain
{R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R) [(Ideal.span {x}).IsPrime] (notMin : ¬Ideal.span {x} ∈ minimalPrimes R) :
    IsDomain R := by

  -- Step : If Ideal.span {x} is not minimal then there exists a minimal prime q properly contiaining Ideal.span {x}
  -- The Mathlib theorem to use here is (`Ideal.exists_minimalPrimes_le`)

  -- Step : Show that q ⊆ Ideal.span {x^n} for all n: By induction let y ∈ q ⊆ (x^n). Then y = rx^n. Since x ∉ q, x^n ∉ q so r ∈ q. Since we
  -- have r ∈ q ⊆ (x), y ∈ (x^(n+1)) and we are done.

  -- Step : Use Krull's Intersection Theorem (`Ideal.iInf_pow_eq_bot_of_localRing`) to show that q = ⊥ (⊥ is the zero ideal and it is written \bot)

  -- Step : Use that q = ⊥ is prime to prove that R is a domain
  sorry


--The dim=n case (stated so that we can use induction): If R is a regular local
--ring of dim R=n, then R is a domain.
theorem IsRegularLocalRing_IsDomain_Fixed_Dim :
    ∀(n : ℕ)(R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (h : IsRegularLocalRing R) (hn : minGenerators (max R) = n), IsDomain R := by
  intro n

  -- We do induction on the number of generators of max R
  induction n with
  | zero =>
    intro R _ _ _ hR hm
    exact IsRegularLocalRing_IsDomain_Dim_zero R hm

  | succ n ih =>
    intro R _ _ _ hR hn
    by_contra hR_not_Dom

    -- Our goal is to show that max R is the union of (max R)^2 along with the minimal primes of R.
    have isMinPrime : ∀(x : R), (x ∈ max R) → (x ∉ (max R)^2) → (Ideal.span {x} ∈ minimalPrimes R) := by
      intro x hx hx2

      have xPrime : (Ideal.span {x}).IsPrime := by
        apply (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp

        have _ : IsLocalRing (R ⧸ (Ideal.span {x})) := by sorry
        -- It will likely be easier to prove this is a seperate lemma. Something like: If R is a local ring and x ∈ max R
        -- then (R ⧸ Ideal.span {x}) is a local ring. Mathlib seems to be lacking in results about quotient rings for the moment.

        have minGenquot : minGenerators (max (R ⧸ (Ideal.span {x}))) = n := by sorry

        have quotReg : IsRegularLocalRing (R ⧸ (Ideal.span {x})) := by sorry
        -- This will likely be the hardest part of the proof. I believe it will require facts about dimension theory that
        -- are being worked on but are not currently in Mathlib. In particualr, I believe we will need:
        -- If R is a noetherian local ring and x ∈ max R then Dim (R ⧸ x) ≥ Dim R - 1
        -- This along with Krull's Height Theorem (This one has been PR'd to Mathlib) applied to minGenquot should prove it.

        exact ih (R ⧸ (Ideal.span {x})) quotReg minGenquot

      by_contra hx3

      exact hR_not_Dom (IsLocalRing_IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain x hx3)

    clear ih

    -- Step : Use xinMin to prove that max R is contained in the union of (max R)^2 and all the minimal primes of R.

    -- Step : Use `minimalPrimes.finite_of_isNoetherianRing` to show the union in the previous step is a finite union.

    -- Step : Apply Prime Avoidance `Ideal.subset_union_prime` to show that (max R) is contained in a minimal prime.

    have dimNotZero : ringKrullDim R ≠ 0 := by
      rw[←hR, ←minGenerators_eq_dimCotangentSpace,hn]
      have : n+1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      exact Nat.cast_ne_zero.mpr this
    -- Step : Use the fact that the Krull Dimension of R is not zero to reach a contradiction.

    sorry


theorem IsRegularLocalRing_IsDomain
{R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (h : IsRegularLocalRing R) :
    IsDomain R := by
  exact IsRegularLocalRing_IsDomain_Fixed_Dim (minGenerators (max R)) R h rfl



#check minimalPrimes.finite_of_isNoetherianRing
#check Ideal.subset_union_prime
#check Ideal.iInf_pow_eq_bot_of_localRing
