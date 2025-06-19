-- This module serves as the root of the `RegularLocalRings` library.
-- Import modules here that should be built as part of the library.

import «RegularLocalRings».Basic
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

--Instance so that Lean knows a quotient of a local ring is a local ring.
instance {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} [Nontrivial (R ⧸ I)] :
    IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

----------------------------------------------------------------------------


----------------------------------------------------------------------------
--Regular local rings

--A regular local ring is a noetherian local ring R with  dim m/m^2 = dim R
class IsRegularLocalRing (R : Type*) [CommRing R] : Prop extends IsLocalRing R, IsNoetherianRing R where
  reg : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R
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


lemma le_minimalPrimes
{R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {P : Ideal R} (hP : P ∈ minimalPrimes R) (hI : I ≤ P) :
    I = P := by

  rw[minimalPrimes_eq_minimals] at hP
  obtain ⟨hP1, hP2⟩ := hP
  have := hP2 ‹_› hI
  exact le_antisymm_iff.mpr ⟨hI, this⟩


--The dim=n case (stated so that we can use induction): If R is a regular local
--ring of dim R=n, then R is a domain.
theorem IsRegularLocalRing_IsDomain_Induction :
    ∀(n : ℕ)(R : Type*) [CommRing R] [IsRegularLocalRing R] (hn : minGenerators (max R) = n), IsDomain R := by
  intro n

  -- We do induction on the number of generators of max R
  induction n with
  | zero =>
    intro R _ hR hm
    exact IsRegularLocalRing_IsDomain_Dim_zero R hm

  | succ n ih =>
    intro R _ hR hn
    by_contra hR_not_Dom

    -- Our goal is to show that max R is the union of (max R)^2 along with the minimal primes of R.
    have isMinPrime : ∀(x : R), (x ∈ max R) → (x ∉ (max R)^2) → (Ideal.span {x} ∈ minimalPrimes R) := by
      intro x hx hx2

      have xPrime : (Ideal.span {x}).IsPrime := by
        apply (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp

        have _ : Nontrivial (R ⧸ (Ideal.span {x})) := Ideal.Quotient.nontrivial (Ideal.span_singleton_ne_top hx)


        have minGenquot : minGenerators (max (R ⧸ (Ideal.span {x}))) = n := by sorry

        have quotReg : IsRegularLocalRing (R ⧸ (Ideal.span {x})) := by sorry
        -- This will likely be the hardest part of the proof. I believe it will require facts about dimension theory that
        -- are being worked on but are not currently in Mathlib. In particualr, I believe we will need:
        -- If R is a noetherian local ring and x ∈ max R then Dim (R ⧸ x) ≥ Dim R - 1
        -- This along with Krull's Height Theorem (This one has been PR'd to Mathlib) applied to minGenquot should prove it.

        exact ih (R ⧸ (Ideal.span {x})) minGenquot

      by_contra hx3

      exact hR_not_Dom (IsLocalRing_IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain x hx3)

    clear ih

    -- Step : Use xinMin to prove that max R is contained in the union of (max R)^2 and all the minimal primes of R.

    -- Step : Use `minimalPrimes.finite_of_isNoetherianRing` to show the union in the previous step is a finite union.

    let S' := (minimalPrimes R) ∪ {(max R)^2}
    have sFin : S'.Finite := Set.Finite.union (minimalPrimes.finite_of_isNoetherianRing R) (Set.finite_singleton ((max R) ^ 2))

    let S := Set.Finite.toFinset sFin

    have hp : (∀ i ∈ S, (i ≠ (max R)^2) → (i ≠ (max R)^2) → i.IsPrime) := by
      intro I hI hm1 _
      have : I ∈ S' := (Set.Finite.mem_toFinset sFin).mp hI
      obtain h1|h2 := this
      exact Ideal.minimalPrimes_isPrime h1
      contradiction

-- Step : Apply Prime Avoidance `Ideal.subset_union_prime` to show that (max R) is contained in a minimal prime
-- or (max R) is contained in (max R)^2
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
  -- Step : Use the fact that the Krull Dimension of R is not zero to reach a contradiction.

    have dimNotZero : ringKrullDim R ≠ 0 := by
      rw[←hR.reg, ←minGenerators_eq_dimCotangentSpace,hn]
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


theorem IsRegularLocalRing_IsDomain
(R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  exact IsRegularLocalRing_IsDomain_Induction (minGenerators (max R)) R rfl



#check minimalPrimes.finite_of_isNoetherianRing
#check Ideal.subset_union_prime
#check Ideal.iInf_pow_eq_bot_of_localRing
