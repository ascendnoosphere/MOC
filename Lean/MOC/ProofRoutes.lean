import MOC.AffineGapCover
import MOC.BilinearPencil
import MOC.ConicSpectralReductions
import MOC.EqualSpectralCoefficients
import MOC.Extremal
import MOC.FourContactRay
import MOC.FourDirectSupportCertificate
import MOC.FourAntipodalSpectra
import MOC.FourTerminalCoverage
import MOC.FreeEigenvalueSlopeSlice
import MOC.GaussianCayley
import MOC.GaussianIntegerDeterminantTest
import MOC.HermitianByNormalFourProof
import MOC.HighContact
import MOC.IsolatedContactFiber
import MOC.MatchingContactRank
import MOC.MobiusOrbitMinimum
import MOC.NormalSupportMaximum
import MOC.NonnormalPoleReduction
import MOC.OrderFourIndependent
import MOC.OrderFiveContact
import MOC.OrderFiveDisjointPairObstruction
import MOC.OrderFiveCommonLawObstruction
import MOC.OrderFivePairMarkers
import MOC.PrincipalCoisometry
import MOC.ReducingCommutant
import MOC.Reformulations
import MOC.SaturatedContactReduction
import MOC.SharpContactRank
import MOC.SpectralMinorDecomposition
import MOC.StationaryDenseCross
import MOC.StationaryPivot
import MOC.TerminalActiveEdges
import MOC.TranslatedDeterminantPowers

/-! A branch belongs here only if there is a Lean proof that it closes its
parent. Open premises within one branch are joined by AND, not OR. -/

open Matrix BigOperators

namespace MOC
namespace ProofRoutes

structure Route (parent : Prop) where
  label : String
  goal : Prop
  close : goal → parent
  isExact : Bool
  reverse : isExact = true → parent → goal

def fromIff {parent goal : Prop} (label : String) (h : goal ↔ parent) :
    Route parent :=
  ⟨label, goal, h.mp, true, fun _ => h.mpr⟩

def sufficient {parent goal : Prop} (label : String) (h : goal → parent) :
    Route parent :=
  ⟨label, goal, h, false, fun hf => by cases hf⟩

/-- Any sufficient source implies each exact target on the same root. -/
theorem Route.implies_exact {P : Prop} (source target : Route P)
    (ht : target.isExact = true) : source.goal → target.goal :=
  fun h => target.reverse ht (source.close h)

/-- Two exact alternatives to the same root are equivalent. -/
theorem Route.iff_exact {P : Prop} (a b : Route P)
    (ha : a.isExact = true) (hb : b.isExact = true) : a.goal ↔ b.goal :=
  ⟨a.implies_exact b hb, b.implies_exact a ha⟩

/-- A refutation transfers back only when the target has a reverse link. -/
theorem Route.refute_exact {P : Prop} (r : Route P) (hr : r.isExact = true)
    (h : ¬ r.goal) : ¬ P := mt (r.reverse hr) h

/-- Existential form of the disjunction of the listed branch goals. -/
def AnyRoute {P : Prop} (routes : List (Route P)) : Prop :=
  ∃ r ∈ routes, r.goal

theorem close_any {P : Prop} {routes : List (Route P)} (h : AnyRoute routes) : P := by
  obtain ⟨r, _, hr⟩ := h
  exact r.close hr

theorem any_iff_of_branch {P Q : Prop} {routes : List (Route P)}
    (name : String) (e : Q ↔ P) (hm : fromIff name e ∈ routes) :
    AnyRoute routes ↔ P :=
  ⟨close_any, fun h => ⟨fromIff name e, hm, e.mpr h⟩⟩

def LabelledAt (n : ℕ) (Sample : Type) : Prop :=
  ∀ (s t : Sample) (f g : Sample → Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → Holds (f s) (g t) U

theorem labelledAt_iff (n : ℕ) (Sample : Type) (sample : Sample) :
    LabelledAt n Sample ↔ Conjecture (Fin n) :=
  ⟨fun h a b U hU => h sample sample (fun _ => a) (fun _ => b) U hU,
   fun h s t f g U hU => h (f s) (g t) U hU⟩

theorem some_labelledAt_iff (n : ℕ) :
    (∃ Sample : Type, Nonempty Sample ∧ LabelledAt n Sample) ↔ Conjecture (Fin n) := by
  constructor
  · rintro ⟨Sample, ⟨sample⟩, h⟩
    exact (labelledAt_iff n Sample sample).mp h
  · intro h
    exact ⟨Unit, ⟨()⟩, (labelledAt_iff n Unit ()).mpr h⟩

/-- Fix one partner entry. The law may depend on all the other input
coordinates and on the mixer; it need not preserve unrelated spectra. -/
def OneEntryLaw (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (j : Fin n) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → ∃ k : ℕ, k ≤ 5 ∧
      ∃ (p : Fin k → Equiv.Perm (Fin n)) (w : Fin k → ℝ),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ z : ℂ,
          (∑ i, (w i : ℂ) * matchingProduct a (Function.update b j z) (p i)) =
            determinantValue a (Function.update b j z) U

theorem oneEntryLaw_iff (n : ℕ) : OneEntryLaw n ↔ Conjecture (Fin n) := by
  constructor
  · intro h a b U hU
    by_cases hn : n = 0
    · subst n
      exact conjecture_zero a b U hU
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have h' := (one_free_partner_entry_iff_common_law a b j U hU).mpr
      (h a b j U hU) (b j)
    simpa only [Function.update_eq_self] using h'
  · intro h a b j U hU
    exact (one_free_partner_entry_iff_common_law a b j U hU).mp
      (fun z => h a (Function.update b j z) U hU)

def NormalMaximizers (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (η : ℂ),
    ∃ U : Matrix (Fin n) (Fin n) ℂ, IsUnitary U ∧
      IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
        (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re

theorem five_of_four_and_normalMaximizers (h₄ : Conjecture (Fin 4))
    (h₅ : NormalMaximizers 5) : Conjecture (Fin 5) :=
  (conjecture_iff_exists_normal_support_maximizer_of_smaller_orders
    (fun m hm => conjecture_of_lt_five h₄ (n := m) hm)).mpr h₅

/-- This branch requires both the one-contact transfer and the support test.
Neither of these alone is listed as an alternative proof of order five. -/
def EightContactStep : Prop :=
  ∀ (U : Matrix (Fin 5) (Fin 5) ℂ), IsUnitary U →
    (∀ i j, U i j ≠ 0) → ∀ v : StrictMatchingSupport U, v.contacts.card < 8 →
      ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card

/-- The universal common-law condition is sufficient but is not an active
branch: the order-five compound-property obstruction is stronger than a
pointwise determinant hull failure. -/
def PositivePairLawFive : Prop :=
  ∀ U : Matrix (Fin 5) (Fin 5) ℂ, IsUnitary U →
    ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
        (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq U I J

theorem not_positivePairLawFive : ¬ PositivePairLawFive := by
  intro h
  obtain ⟨w, hw, hm⟩ := h orderFiveFlatReflection unitary_orderFiveFlatReflection
  have hEq := (orderFive_weighted_spectra_eq_all_iff_doubleton_images _
    unitary_orderFiveFlatReflection w).mpr hm
  have hs := (orderFive_weighted_spectra_eq_all_iff_pair_images _
    unitary_orderFiveFlatReflection w).mp hEq |>.1
  exact orderFiveFlatReflection_no_positive_pair_law ⟨w, hw, hs, hm⟩

theorem five_of_positivePairLaw (h : PositivePairLawFive) : Conjecture (Fin 5) := by
  intro a b U hU
  obtain ⟨w, hw, hm⟩ := h U hU
  have hEq := (orderFive_weighted_spectra_eq_all_iff_doubleton_images U hU w).mpr hm
  have hmass := (orderFive_weighted_spectra_eq_all_iff_pair_images U hU w).mp hEq |>.1
  exact holds_of_weights w hw hmass (hEq a b)

theorem conjecture_of_contact_step {n k : ℕ}
    (step : ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ i j, U i j ≠ 0) → ∀ v : StrictMatchingSupport U, v.contacts.card < k →
        ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card)
    (bound : Reformulations.ContactForm n k) : Conjecture (Fin n) := by
  intro a b U hU
  apply (holds_all_unitaries_iff_full_support a b).mpr _ U hU
  intro V hV hfull
  by_contra hbad
  obtain ⟨w⟩ := nonempty_strictMatchingSupport_of_failure a b hbad
  obtain ⟨v, hv⟩ := exists_strictMatchingSupport_at_least k w (step V hV hfull)
  exact (not_le_of_gt v.strict) (bound v.a v.b V v.η v.pivot hV v.maximal hv)

def SixContactStep : Prop :=
  ∀ (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U →
    (∀ i j, U i j ≠ 0) → ∀ v : StrictMatchingSupport U, v.contacts.card < 6 →
      ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card

def of_witness_iff {P Bad : Prop} (label : String) (e : (¬ P) ↔ Bad) : Route P :=
  fromIff label ((not_congr e).symm.trans not_not)

theorem contact_step_of_le_sharp_threshold {n k : ℕ} (hk : k ≤ 2 * n - 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (_ : ∀ i j, U i j ≠ 0)
    (w : StrictMatchingSupport U) (hw : w.contacts.card < k) :
    ∃ v : StrictMatchingSupport U, w.contacts.card < v.contacts.card := by
  have hbound : w.contacts.card ≤ 2 * Fintype.card (Fin n) - 2 := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨v, _, _, hinc, _⟩ := global_varying_gap_contact_transfer
    (affineGapContinuation (Equiv.Perm (Fin n))) hU w hbound
  exact ⟨v, Finset.card_lt_card hinc⟩

/-- These tests apply at each order in the open range. The order can
be fixed before a proof chooses a test. -/
@[irreducible] def orderRoutes (n : ℕ) (hn : 4 ≤ n) : List (Route (Conjecture (Fin n))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact [fromIff "Normal complex matrices" conjecture_iff_normalConjecture.symm,
    fromIff "One-entry positive laws" (oneEntryLaw_iff n),
    fromIff "One free eigenvalue with at most three slopes" (freeEigenvalueSlopeSliceTest_iff n),
    fromIff "Translated distance for spectra in the open unit disk"
      (conjecture_iff_local_translated_normSq 1 zero_lt_one).symm,
    fromIff "Translated power sums for spectra in the open unit disk"
      (conjecture_iff_local_translated_power_sums 1 zero_lt_one).symm,
    fromIff "Evaluated finite spectral comparison" (some_labelledAt_iff n),
    fromIff "Equal traces" conjecture_iff_equal_trace.symm,
    fromIff "Equal second elementary coefficients" conjecture_iff_equal_second_elementary.symm,
    fromIff "Equal first and second elementary coefficients"
      conjecture_iff_equal_first_second_elementary.symm,
    fromIff "Real-part bound" conjecture_iff_real_bound.symm,
    fromIff "Nonopposite spectra" conjecture_iff_nonopposite.symm,
    fromIff "Regular matching products" conjecture_iff_regular_matching_products.symm,
    fromIff "Regular spectra and full-support mixers" conjecture_iff_regular_spectra_full_support.symm,
    fromIff "Bilinear pencil" conjecture_iff_bilinear_pencil.symm,
    fromIff "Balanced spectra with a nonnormal sum" conjecture_iff_balanced_nonnormal.symm,
    fromIff "Möbius-balanced regular spectra"
      (conjecture_iff_mobius_balanced_regular (ι := Fin n) (by rw [Fintype.card_fin]; omega)).symm,
    fromIff "Anchored spectra" (Reformulations.conjecture_iff_anchored_regular (n := n) ⟨0, by omega⟩).symm,
    fromIff "Three-anchor rank-one kernel"
      (Reformulations.conjecture_iff_three_anchor_kernel (n := n) ⟨0, by omega⟩ ⟨1, by omega⟩
        ⟨0, by omega⟩ (fun h => Nat.zero_ne_one (congrArg Fin.val h))).symm,
    fromIff "Nonzero contact-saturated support bound" conjecture_iff_contact_saturated_bound.symm,
    fromIff "Global contact bound" conjecture_iff_global_contact_bound.symm,
    fromIff "Balanced global contact bound" conjecture_iff_balanced_global_contact_bound.symm,
    fromIff "Contact bound with rank and moments" conjecture_iff_rank_moment_global_contact_bound.symm,
    fromIff "Contact bound with isolation, rank and moments"
      conjecture_iff_isolated_rank_moment_contact_bound.symm,
    fromIff "Sharp terminal contact bound" conjecture_iff_sharp_terminal_contact_bound.symm,
    fromIff "Sharp contact rank bound" conjecture_iff_sharp_contact_rank_bound.symm,
    fromIff "Sharp contact bound with isolation, rank and moments"
      conjecture_iff_sharp_isolated_rank_moment_contact_bound.symm,
    fromIff "Terminal stationary witnesses with negative pivots"
      conjecture_iff_terminal_negative_pivots.symm,
    fromIff "Support without a common active edge"
      conjecture_iff_support_without_common_active_edge.symm]

theorem order_routes_iff (n : ℕ) (hn : 4 ≤ n) :
    AnyRoute (orderRoutes n hn) ↔ Conjecture (Fin n) := by
  apply any_iff_of_branch "Normal complex matrices" conjecture_iff_normalConjecture.symm
  unfold orderRoutes
  exact List.mem_cons_self

def fourRoutes : List (Route (Conjecture (Fin 4))) :=
  [fromIff "Real orthogonal mixers with complex spectra" conjecture_four_iff_orthogonal.symm,
   fromIff "Regular orthogonal support maximizers"
      conjecture_four_iff_regular_orthogonal_support_maxima.symm,
   fromIff "Normal sum at a support maximizer" conjecture_four_iff_exists_normal_support_maximizer.symm,
   fromIff "Principal coisometry of dimension three" (conjecture_iff_principalCoisometry 3).symm,
   fromIff "Rectangular compression with three rows" (conjecture_iff_rectangularCompression 3).symm,
   fromIff "Regular orthogonal inclusion" Reformulations.conjecture_four_iff_regularOrthogonal.symm,
   of_witness_iff "Exclude all regular stationary orthogonal witnesses"
      not_conjecture_four_iff_regular_stationary_orthogonal_witness,
   of_witness_iff "Exclude regular stationary witnesses with a full row and column"
      not_conjecture_four_iff_dense_cross_stationary_witness,
   fromIff "Exclude orthogonal witnesses with seven contacts"
      conjecture_four_iff_seven_orthogonal_contacts.symm,
   fromIff "Exclude stationary orthogonal witnesses with seven contacts"
      conjecture_four_iff_terminal_stationary_pivots.symm,
   fromIff "Exclude regular terminal orthogonal witnesses"
      conjecture_four_iff_no_regular_terminal_orthogonal_witness.symm,
   fromIff "Exclude regular terminal witnesses with canonical mixed cost"
      conjecture_four_iff_no_canonical_mixed_terminal_witness.symm,
   fromIff "Six-contact support test"
      ⟨conjecture_of_contact_step (show SixContactStep from
        contact_step_of_le_sharp_threshold (n := 4) (k := 6) (by decide)), Reformulations.contactForm_of_conjecture⟩,
   fromIff "Distinct spectra outside circles and lines" conjecture_four_iff_noncircular.symm,
   fromIff "Antipodal half-disk with real orthogonal mixers"
     conjecture_four_iff_antipodal_halfDisk_orthogonal.symm,
   fromIff "First spectrum on the standard parabola"
      (conjecture_iff_spectralCurveTest four_spectralParabola_test_iff).symm,
   fromIff "First spectrum on the standard hyperbola"
      (conjecture_iff_spectralCurveTest (four_spectralHyperbola_test_iff Complex.I 1 (by simp))).symm,
   fromIff "First spectrum on the ellipse at the semiaxis threshold"
      (conjecture_iff_spectralCurveTest (four_spectralEllipse_test_iff (2 + Real.sqrt 3) le_rfl)).symm,
   fromIff "Signed support gap on the bilinear chart" conjecture_four_iff_bilinear_support.symm] ++
    orderRoutes 4 le_rfl

def fiveRoutes : List (Route (Conjecture (Fin 5))) :=
  [fromIff "Principal coisometry of dimension four" (conjecture_iff_principalCoisometry 4).symm,
   fromIff "Rectangular compression with four rows" (conjecture_iff_rectangularCompression 4).symm,
   sufficient "Order four AND existence of normal order-five maximizers"
      (fun h : Conjecture (Fin 4) ∧ NormalMaximizers 5 =>
        five_of_four_and_normalMaximizers h.1 h.2),
   fromIff "Eight-contact support test with a full-support mixer"
      (conjecture_five_iff_fullSupportEight_of_step (show EightContactStep from
        contact_step_of_le_sharp_threshold (n := 5) (k := 8) (by decide))).symm,
   fromIff "First spectrum on the standard parabola"
      (conjecture_iff_spectralCurveTest five_spectralParabola_test_iff).symm,
   fromIff "First spectrum on the standard hyperbola"
      (conjecture_iff_spectralCurveTest (five_spectralHyperbola_test_iff Complex.I 1 (by simp))).symm,
   -- The universal disjoint-pair certificate is refuted by the translated real spectra.
   sufficient "Orthogonal minor convexification AND orthogonal order five"
      (fun h : TwoOrthogonalMinorTables (Fin 5) ∧ OrthogonalConjecture (Fin 5) =>
        (conjecture_iff_orthogonal_of_minor_convexification h.1).mpr h.2)] ++
    orderRoutes 5 (by decide)

theorem four_routes_iff : AnyRoute fourRoutes ↔ Conjecture (Fin 4) :=
  any_iff_of_branch _ conjecture_four_iff_orthogonal.symm (List.mem_cons_self ..)

theorem five_routes_iff : AnyRoute fiveRoutes ↔ Conjecture (Fin 5) :=
  any_iff_of_branch _ (conjecture_iff_principalCoisometry 4).symm (List.mem_cons_self ..)

/-- Solving orders four and five leaves the orders at least six. -/
theorem all_iff_four_and_five_and_higher :
    MOCIsTrue ↔ Conjecture (Fin 4) ∧ Conjecture (Fin 5) ∧
      ∀ n, 6 ≤ n → Conjecture (Fin n) := by
  refine ⟨fun h => ⟨h 4, h 5, fun n _ => h n⟩, ?_⟩
  rintro ⟨h4, h5, hhi⟩
  apply mocIsTrue_iff_from_four.mpr
  intro n hn
  by_cases h : n = 4
  · subst n
    exact h4
  by_cases h : n = 5
  · subst n
    exact h5
  exact hhi n (by omega)

open Reformulations

/-- The terminal contact support bound in every order is equivalent to MOC. -/
theorem moc_iff_contact_saturated_bounds :
    MOCIsTrue ↔ ∀ n : ℕ, ContactSaturatedBound (Fin n) :=
  forall_congr' fun _ => conjecture_iff_contact_saturated_bound

@[irreducible] def nativeRoutes : List (Route MOCIsTrue) :=
  [fromIff "Normal complex matrices" moc_iff_complexMatrices.symm,
   fromIff "Normal eigenframes" moc_iff_normalFrames.symm,
   fromIff "Nonnormal inputs with normal spectral representatives"
      moc_iff_nonnormalSpectralRepresentatives.symm,
   fromIff "Commuting tuple scalar projections" moc_iff_commutingTupleProjections.symm,
   fromIff "Normalized pencils" moc_iff_normalizedPencils.symm,
   fromIff "Complex base change of commutative-ring matrices" moc_iff_commutativeRingMatrices.symm,
   fromIff "Exterior-power spectra" moc_iff_exteriorSpectrum.symm,
   fromIff "Symmetric-power spectra" moc_iff_symmetricSpectrum.symm,
   fromIff "Tensor spectra" moc_iff_tensorSpectrum.symm,
   fromIff "Direct sum" moc_iff_directSumSpectrum.symm,
   fromIff "Kronecker sum" moc_iff_kroneckerSumSpectrum.symm,
   fromIff "Selected adjoint spectrum" moc_iff_selectedAdjointSpectrum.symm,
   fromIff "Selected conjugation spectra" moc_iff_selectedConjugationSpectrum.symm,
   fromIff "Finite mixed discriminant" moc_iff_pointwiseMixedDiscriminant.symm,
   fromIff "Normal left regular representations" moc_iff_nativeLeftRegularAlgebra.symm,
   fromIff "Frobenius algebra" moc_iff_nativeFrobeniusAlgebra.symm,
   fromIff "Monic matrix polynomial roots" moc_iff_nativeMonicMatrixPolynomialRoots.symm,
   fromIff "Top exterior power" moc_iff_nativeTopExteriorHull.symm,
   fromIff "Complex scalar extension and splitting" moc_iff_nativeSplitScalarExtension.symm,
   fromIff "Division ring block representations" moc_iff_nativeDivisionBlockHull.symm,
   fromIff "Finite complex representation" moc_iff_nativeComplexAlgebraRepresentation.symm,
   fromIff "Finite star representation" moc_iff_nativeStarAlgebraRepresentation.symm,
   fromIff "Finite Fredholm determinant" moc_iff_nativeFiniteFredholmHull.symm,
   fromIff "Finite regularized determinant at order two" moc_iff_nativeFiniteRegularizedTwoHull.symm,
   fromIff "Finite atomic normalized kernel" moc_iff_nativeFiniteAtomicKernelHull.symm,
   fromIff "Finite perturbation determinant" NativeFirstB.finitePerturbationForm_iff,
   fromIff "Exponentiated determinant path" determinantPathForm_iff,
   fromIff "Finite chain endomorphisms" NativeFirstB.chainTermForm_iff,
   fromIff "Invertible normal projective lifts" NativeLinksB.projectiveLiftForm_iff,
   fromIff "Actual integral torus characters" NativeLinksB.torusCharacterForm_iff,
   fromIff "Joint Hermitian integrals" NativeLinksB.quantumIntegralsForm_iff,
   fromIff "Gaussian integer spectra" NativeLinksB.gaussianSpectrumForm_iff,
   fromIff "Division-free Gaussian integer determinant comparisons"
     mocIsTrue_iff_gaussianIntegerDeterminantTest.symm,
   fromIff "Gaussian integer spectra and Gaussian rational mixers"
      mocIsTrue_iff_gaussian_spectra_rational_mixer.symm,
   fromIff "Affine linear parts" moc_iff_affineLinearParts.symm,
   fromIff "Actual affine derivatives" NativeFirstB.affineDerivativeForm_iff,
   fromIff "Nonzero spectra" moc_iff_nonzeroSpectra.symm,
   fromIff "Invertible projective diagonal lifts" moc_iff_projectiveDiagonalLifts.symm,
   fromIff "Traceless Cartan spectra" tracelessCartanForm_iff,
   fromIff "Newton monomials" newtonMonomialForm_iff,
   fromIff "Projective toric section weights" projectiveToricSectionForm_iff,
   fromIff "Loopless complex directed adjacency" looplessDirectedAdjacencyForm_iff,
   fromIff "Constant-generator monodromy" constantMonodromyForm_iff,
   fromIff "Finite bipartite matching" bipartiteMatchingForm_iff,
   fromIff "Weighted bipartite determinant" weightedBipartiteMatchingForm_iff,
   fromIff "Finite Euler determinant" finiteEulerForm_iff,
   fromIff "Finite Euler determinant at parameter one"
      (fixedEulerParameterForm_iff (z := 1) one_ne_zero),
   fromIff "Normal word products" normalWordProductForm_iff,
   fromIff "Almost-sure finite spectra" almostSureSpectralForm_iff,
   fromIff "Joint tuple projections" jointTupleProjectionForm_iff,
   fromIff "Invertible representatives" invertibleRepresentativeForm_iff,
   fromIff "C-star matrix form" CStar.matrixForm_iff,
   fromIff "C-star orbit form" CStar.orbitForm_iff,
   fromIff "C-star commuting determinants" commutantForm_iff,
   fromIff "C-star integer coupling form" couplingForm_iff,
   fromIff "C-star Cartesian form" CStar.cartesianForm_iff,
   fromIff "C-star functional calculus" CStar.functionalCalculusForm_iff,
   fromIff "C-star affine form" CStar.affineForm_iff,
   fromIff "C-star pointwise characteristic form" CStar.pointwiseCharacteristicForm_iff,
   fromIff "Pointwise characteristic polynomial of the spectral sum" pointwiseCharacteristicForm_iff,
   fromIff "C-star scalar weight form" CStar.scalarWeightForm_iff,
   fromIff "Paired finite star representations" CStar.pairedStarRepresentationForm_iff,
   fromIff "Compound form" compoundForm_iff,
   fromIff "Traceless real-part bound" moc_iff_traceless_real_bound.symm,
   fromIff "Regular anchored spectra" moc_iff_anchored_regular.symm,
   fromIff "Three-anchor rank-one kernel in all orders" moc_iff_three_anchor_kernel.symm,
   fromIff "Nonzero contact-saturated support bounds in every order"
      moc_iff_contact_saturated_bounds.symm,
   fromIff "Normal maximizers in every order" mocIsTrue_iff_exists_normal_support_maximizer.symm,
   fromIff "Principal coisometries in all orders" mocIsTrue_iff_principalCoisometry.symm,
   fromIff "No paired block split" mocIsTrue_iff_no_proper_paired_blocks.symm,
   fromIff "Every row and column has degree at least three"
      mocIsTrue_iff_support_degree_at_least_three.symm,
   fromIff "Strict support expansion" mocIsTrue_iff_strict_support_expansion.symm,
   fromIff "Balanced spectra and strict support expansion" mocIsTrue_iff_balanced_expanding.symm,
   fromIff "Scalar common commutant" mocIsTrue_iff_scalar_common_commutant.symm,
   fromIff "Regular spectra with scalar common commutant"
      mocIsTrue_iff_regular_scalar_common_commutant.symm,
   fromIff "Regular scalar common commutant and nonnormal poles"
      mocIsTrue_iff_regular_scalar_nonnormal_poles.symm,
   fromIff "Terminal matching chart support" mocIsTrue_iff_terminal_chart_support.symm,
   fromIff "Terminal matching chart with 2n-1 contacts"
      mocIsTrue_iff_terminal_chart_support_twice_minus_one.symm,
   fromIff "Terminal matching chart with old gap rank"
      mocIsTrue_iff_terminal_chart_support_old_gap_rank.symm,
   fromIff "Terminal matching chart with old gap rank and no common active edge"
      mocIsTrue_iff_terminal_chart_support_old_gap_rank_no_common_edge.symm,
   fromIff "Terminal matching chart with constraint rank"
      mocIsTrue_iff_terminal_chart_support_of_constraint_rank.symm,
   fromIff "Terminal matching chart with minimal prime isolation"
      mocIsTrue_iff_terminal_chart_support_minimal_prime.symm,
   fromIff "All three order ranges" all_iff_four_and_five_and_higher.symm,
   sufficient "Regular contact covers AND terminal chart support"
      (And.elim mocIsTrue_of_regular_contact_covers),
   sufficient "Separate characteristic coefficients" CStar.moc_of_separateCoefficientForm,
   sufficient "Simultaneous mixed-pencil coefficients" moc_of_simultaneousMixedPencilHull]

private theorem normal_mem_nativeRoutes :
    fromIff "Normal complex matrices" moc_iff_complexMatrices.symm ∈ nativeRoutes := by
  unfold nativeRoutes
  exact List.mem_cons_self

theorem native_routes_iff : AnyRoute nativeRoutes ↔ MOCIsTrue :=
  any_iff_of_branch "Normal complex matrices" moc_iff_complexMatrices.symm normal_mem_nativeRoutes

/-- Each route permits arbitrary complex evaluations of labelled finite
samples. It uses an equivalence between that evaluated spectral comparison
and the unrestricted Marcus–de Oliveira conjecture. -/
@[irreducible] def labelledRoutes : List (Route MOCIsTrue) :=
  [fromIff "Complex matrices (finite labelled spectral form)" atlas001Labelled_iff,
fromIff "Normal matrices (finite labelled spectral form)" atlas002Labelled_iff,
fromIff "Hermitian matrices (finite labelled spectral form)" atlas003Labelled_iff,
fromIff "Positive definite matrices (finite labelled spectral form)" atlas004Labelled_iff,
fromIff "Unitary matrices (finite labelled spectral form)" atlas005Labelled_iff,
fromIff "Nonnormal matrices (finite labelled spectral form)" atlas006Labelled_iff,
fromIff "Rectangular maps (finite labelled spectral form)" atlas007Labelled_iff,
fromIff "Commuting normal tuple (finite labelled spectral form)" atlas008Labelled_iff,
fromIff "Regular matrix pencils (finite labelled spectral form)" atlas009Labelled_iff,
fromIff "Monic matrix polynomials (finite labelled spectral form)" atlas010Labelled_iff,
fromIff "Real skew-symmetric matrices (finite labelled spectral form)" atlas011Labelled_iff,
fromIff "Commutative-ring matrices (finite labelled spectral form)" atlas012Labelled_iff,
fromIff "Exterior power (finite labelled spectral form)" atlas013Labelled_iff,
fromIff "Top exterior power (finite labelled spectral form)" atlas014Labelled_iff,
fromIff "Symmetric power (finite labelled spectral form)" atlas015Labelled_iff,
fromIff "Tensor product (finite labelled spectral form)" atlas016Labelled_iff,
fromIff "Direct sum (finite labelled spectral form)" atlas017Labelled_iff,
fromIff "Kronecker sum (finite labelled spectral form)" atlas018Labelled_iff,
fromIff "Endomorphism algebra, adjoint action (finite labelled spectral form)" atlas019Labelled_iff,
fromIff "Conjugation action (finite labelled spectral form)" atlas020Labelled_iff,
fromIff "Tensor algebraic eigenvalues (finite labelled spectral form)" atlas021Labelled_iff,
fromIff "Tensor Z-eigenvalues (finite labelled spectral form)" atlas022Labelled_iff,
fromIff "GKZ hyperdeterminant (finite labelled spectral form)" atlas023Labelled_iff,
fromIff "Gram matrices (finite labelled spectral form)" atlas024Labelled_iff,
fromIff "Finite associative unital algebra (finite labelled spectral form)" atlas025Labelled_iff,
fromIff "Finite commutative algebra (finite labelled spectral form)" atlas026Labelled_iff,
fromIff "Central simple algebra (finite labelled spectral form)" atlas027Labelled_iff,
fromIff "Quaternion algebra (finite labelled spectral form)" atlas028Labelled_iff,
fromIff "Quaternionic matrices (finite labelled spectral form)" atlas029Labelled_iff,
fromIff "Division-ring matrices (finite labelled spectral form)" atlas030Labelled_iff,
fromIff "Octonion algebra (finite labelled spectral form)" atlas031Labelled_iff,
fromIff "Clifford algebra (finite labelled spectral form)" atlas032Labelled_iff,
fromIff "Finite group algebra (finite labelled spectral form)" atlas033Labelled_iff,
fromIff "Frobenius algebra (finite labelled spectral form)" atlas034Labelled_iff,
fromIff "Polynomial quotient (finite labelled spectral form)" atlas035Labelled_iff,
fromIff "Finite projective module (finite labelled spectral form)" atlas036Labelled_iff,
fromIff "Euclidean Jordan algebra (finite labelled spectral form)" atlas037Labelled_iff,
fromIff "Real symmetric Jordan algebra (finite labelled spectral form)" atlas038Labelled_iff,
fromIff "Complex Hermitian Jordan algebra (finite labelled spectral form)" atlas039Labelled_iff,
fromIff "Quaternionic Hermitian Jordan algebra (finite labelled spectral form)" atlas040Labelled_iff,
fromIff "Albert algebra (finite labelled spectral form)" atlas041Labelled_iff,
fromIff "Spin factor (finite labelled spectral form)" atlas042Labelled_iff,
fromIff "Symmetric cones (finite labelled spectral form)" atlas043Labelled_iff,
fromIff "Hyperbolic polynomial (finite labelled spectral form)" atlas044Labelled_iff,
fromIff "Elementary symmetric cones (finite labelled spectral form)" atlas045Labelled_iff,
fromIff "Determinant barrier theory (finite labelled spectral form)" atlas046Labelled_iff,
fromIff "Spectral convex analysis (finite labelled spectral form)" atlas047Labelled_iff,
fromIff "Mixed discriminants (finite labelled spectral form)" atlas048Labelled_iff,
fromIff "Banach-space operators (finite labelled spectral form)" atlas049Labelled_iff,
fromIff "Hilbert-space operators (finite labelled spectral form)" atlas050Labelled_iff,
fromIff "Unital Banach algebra (finite labelled spectral form)" atlas051Labelled_iff,
fromIff "Commutative C-star algebra C(X) (finite labelled spectral form)" atlas052Labelled_iff,
fromIff "Unital C-star algebra (finite labelled spectral form)" atlas053Labelled_iff,
fromIff "Normal C-star element (finite labelled spectral form)" atlas054Labelled_iff,
fromIff "Finite von Neumann algebra (finite labelled spectral form)" atlas055Labelled_iff,
fromIff "Type II1 factor (finite labelled spectral form)" atlas056Labelled_iff,
fromIff "Semifinite von Neumann algebra (finite labelled spectral form)" atlas057Labelled_iff,
fromIff "Group von Neumann algebra (finite labelled spectral form)" atlas058Labelled_iff,
fromIff "Free probability (finite labelled spectral form)" atlas059Labelled_iff,
fromIff "Calkin algebra (finite labelled spectral form)" atlas060Labelled_iff,
fromIff "Compact operators (finite labelled spectral form)" atlas061Labelled_iff,
fromIff "Trace-class operators (finite labelled spectral form)" atlas062Labelled_iff,
fromIff "Hilbert-Schmidt operators (finite labelled spectral form)" atlas063Labelled_iff,
fromIff "Schatten classes (finite labelled spectral form)" atlas064Labelled_iff,
fromIff "Integral operators (finite labelled spectral form)" atlas065Labelled_iff,
fromIff "Elliptic operators on closed manifolds (finite labelled spectral form)" atlas066Labelled_iff,
fromIff "Pseudodifferential calculus (finite labelled spectral form)" atlas067Labelled_iff,
fromIff "Spectral triples (finite labelled spectral form)" atlas068Labelled_iff,
fromIff "Dixmier trace theory (finite labelled spectral form)" atlas069Labelled_iff,
fromIff "De la Harpe-Skandalis determinant (finite labelled spectral form)" atlas070Labelled_iff,
fromIff "Perturbation determinants (finite labelled spectral form)" atlas071Labelled_iff,
fromIff "Scattering theory (finite labelled spectral form)" atlas072Labelled_iff,
fromIff "Chain complexes (finite labelled spectral form)" atlas073Labelled_iff,
fromIff "Singular homology (finite labelled spectral form)" atlas074Labelled_iff,
fromIff "Singular cohomology (finite labelled spectral form)" atlas075Labelled_iff,
fromIff "Simplicial homology (finite labelled spectral form)" atlas076Labelled_iff,
fromIff "Cellular homology (finite labelled spectral form)" atlas077Labelled_iff,
fromIff "De Rham cohomology (finite labelled spectral form)" atlas078Labelled_iff,
fromIff "Dolbeault cohomology (finite labelled spectral form)" atlas079Labelled_iff,
fromIff "Hodge theory (finite labelled spectral form)" atlas080Labelled_iff,
fromIff "Intersection homology (finite labelled spectral form)" atlas081Labelled_iff,
fromIff "Group homology (finite labelled spectral form)" atlas082Labelled_iff,
fromIff "Group cohomology (finite labelled spectral form)" atlas083Labelled_iff,
fromIff "Sheaf cohomology (finite labelled spectral form)" atlas084Labelled_iff,
fromIff "Hypercohomology (finite labelled spectral form)" atlas085Labelled_iff,
fromIff "Hochschild homology (finite labelled spectral form)" atlas086Labelled_iff,
fromIff "Hochschild cohomology (finite labelled spectral form)" atlas087Labelled_iff,
fromIff "Cyclic homology (finite labelled spectral form)" atlas088Labelled_iff,
fromIff "Equivariant cohomology (finite labelled spectral form)" atlas089Labelled_iff,
fromIff "L2-homology (finite labelled spectral form)" atlas090Labelled_iff,
fromIff "Persistent homology (finite labelled spectral form)" atlas091Labelled_iff,
fromIff "Spectral sequences (finite labelled spectral form)" atlas092Labelled_iff,
fromIff "Superalgebra (finite labelled spectral form)" atlas093Labelled_iff,
fromIff "Perfect complexes (finite labelled spectral form)" atlas094Labelled_iff,
fromIff "Reidemeister torsion (finite labelled spectral form)" atlas095Labelled_iff,
fromIff "Ray-Singer analytic torsion (finite labelled spectral form)" atlas096Labelled_iff,
fromIff "L2-torsion (finite labelled spectral form)" atlas097Labelled_iff,
fromIff "Lefschetz fixed-point theory (finite labelled spectral form)" atlas098Labelled_iff,
fromIff "Euclidean linear deformation (finite labelled spectral form)" atlas099Labelled_iff,
fromIff "Affine geometry (finite labelled spectral form)" atlas100Labelled_iff,
fromIff "Projective geometry (finite labelled spectral form)" atlas101Labelled_iff,
fromIff "Differential topology (finite labelled spectral form)" atlas102Labelled_iff,
fromIff "Riemannian geometry (finite labelled spectral form)" atlas103Labelled_iff,
fromIff "Pseudo-Riemannian geometry (finite labelled spectral form)" atlas104Labelled_iff,
fromIff "Hypersurface geometry (finite labelled spectral form)" atlas105Labelled_iff,
fromIff "Ricci geometry (finite labelled spectral form)" atlas106Labelled_iff,
fromIff "Curvature operator (finite labelled spectral form)" atlas107Labelled_iff,
fromIff "Kähler geometry (finite labelled spectral form)" atlas108Labelled_iff,
fromIff "Finsler geometry (finite labelled spectral form)" atlas109Labelled_iff,
fromIff "Hessian and Monge-Ampere geometry (finite labelled spectral form)" atlas110Labelled_iff,
fromIff "Geometric measure theory (finite labelled spectral form)" atlas111Labelled_iff,
fromIff "Symplectic linear maps (finite labelled spectral form)" atlas112Labelled_iff,
fromIff "Williamson theory (finite labelled spectral form)" atlas113Labelled_iff,
fromIff "Hamiltonian linearization (finite labelled spectral form)" atlas114Labelled_iff,
fromIff "Hamiltonian torus actions (finite labelled spectral form)" atlas115Labelled_iff,
fromIff "Symplectic toric geometry (finite labelled spectral form)" atlas116Labelled_iff,
fromIff "Geometric invariant theory (finite labelled spectral form)" atlas117Labelled_iff,
fromIff "Contact geometry (finite labelled spectral form)" atlas118Labelled_iff,
fromIff "Geometric quantization (finite labelled spectral form)" atlas119Labelled_iff,
fromIff "Poisson geometry (finite labelled spectral form)" atlas120Labelled_iff,
fromIff "Floer homology (finite labelled spectral form)" atlas121Labelled_iff,
fromIff "Maslov index theory (finite labelled spectral form)" atlas122Labelled_iff,
fromIff "Hamiltonian integrable systems (finite labelled spectral form)" atlas123Labelled_iff,
fromIff "Commutative algebra and schemes (finite labelled spectral form)" atlas124Labelled_iff,
fromIff "Algebraic varieties (finite labelled spectral form)" atlas125Labelled_iff,
fromIff "Vector bundles (finite labelled spectral form)" atlas126Labelled_iff,
fromIff "Line bundles (finite labelled spectral form)" atlas127Labelled_iff,
fromIff "Higgs bundles (finite labelled spectral form)" atlas128Labelled_iff,
fromIff "Harder-Narasimhan filtration (finite labelled spectral form)" atlas129Labelled_iff,
fromIff "Toric algebraic geometry (finite labelled spectral form)" atlas130Labelled_iff,
fromIff "Newton-Okounkov theory (finite labelled spectral form)" atlas131Labelled_iff,
fromIff "Intersection theory (finite labelled spectral form)" atlas132Labelled_iff,
fromIff "Chern-Weil theory (finite labelled spectral form)" atlas133Labelled_iff,
fromIff "Virtual enumerative geometry (finite labelled spectral form)" atlas134Labelled_iff,
fromIff "Arakelov geometry (finite labelled spectral form)" atlas135Labelled_iff,
fromIff "Finite separable field extensions (finite labelled spectral form)" atlas136Labelled_iff,
fromIff "Galois representations (finite labelled spectral form)" atlas137Labelled_iff,
fromIff "Local fields (finite labelled spectral form)" atlas138Labelled_iff,
fromIff "Newton polygons (finite labelled spectral form)" atlas139Labelled_iff,
fromIff "Crystalline cohomology (finite labelled spectral form)" atlas140Labelled_iff,
fromIff "Filtered phi-modules (finite labelled spectral form)" atlas141Labelled_iff,
fromIff "Etale cohomology over finite fields (finite labelled spectral form)" atlas142Labelled_iff,
fromIff "Weil zeta functions (finite labelled spectral form)" atlas143Labelled_iff,
fromIff "Motivic theory (finite labelled spectral form)" atlas144Labelled_iff,
fromIff "Local L-factors (finite labelled spectral form)" atlas145Labelled_iff,
fromIff "Mahler measure (finite labelled spectral form)" atlas146Labelled_iff,
fromIff "Discriminants (finite labelled spectral form)" atlas147Labelled_iff,
fromIff "Finite group representations (finite labelled spectral form)" atlas148Labelled_iff,
fromIff "Lie algebra representations (finite labelled spectral form)" atlas149Labelled_iff,
fromIff "Highest-weight theory (finite labelled spectral form)" atlas150Labelled_iff,
fromIff "Root systems (finite labelled spectral form)" atlas151Labelled_iff,
fromIff "Weyl group representations (finite labelled spectral form)" atlas152Labelled_iff,
fromIff "Compact-group harmonic analysis (finite labelled spectral form)" atlas153Labelled_iff,
fromIff "Abelian Fourier analysis (finite labelled spectral form)" atlas154Labelled_iff,
fromIff "Hecke algebras (finite labelled spectral form)" atlas155Labelled_iff,
fromIff "Satake parameters (finite labelled spectral form)" atlas156Labelled_iff,
fromIff "Tensor categories of representations (finite labelled spectral form)" atlas157Labelled_iff,
fromIff "Association schemes (finite labelled spectral form)" atlas158Labelled_iff,
fromIff "Spherical harmonic analysis (finite labelled spectral form)" atlas159Labelled_iff,
fromIff "Convex bodies (finite labelled spectral form)" atlas160Labelled_iff,
fromIff "Polar convexity (finite labelled spectral form)" atlas161Labelled_iff,
fromIff "Zonotopes (finite labelled spectral form)" atlas162Labelled_iff,
fromIff "Mixed volumes (finite labelled spectral form)" atlas163Labelled_iff,
fromIff "Matroid theory (finite labelled spectral form)" atlas164Labelled_iff,
fromIff "Oriented matroids (finite labelled spectral form)" atlas165Labelled_iff,
fromIff "Valuated matroids (finite labelled spectral form)" atlas166Labelled_iff,
fromIff "Tropical min-plus matrices (finite labelled spectral form)" atlas167Labelled_iff,
fromIff "Tropical polynomials (finite labelled spectral form)" atlas168Labelled_iff,
fromIff "Newton polytopes (finite labelled spectral form)" atlas169Labelled_iff,
fromIff "Bergman fans and tropical linear spaces (finite labelled spectral form)" atlas170Labelled_iff,
fromIff "Convex optimization and semidefinite programming (finite labelled spectral form)" atlas171Labelled_iff,
fromIff "Spectral graph theory (finite labelled spectral form)" atlas172Labelled_iff,
fromIff "Graph Laplacians (finite labelled spectral form)" atlas173Labelled_iff,
fromIff "Normalized graph Laplacians (finite labelled spectral form)" atlas174Labelled_iff,
fromIff "Directed graph spectra (finite labelled spectral form)" atlas175Labelled_iff,
fromIff "Graph Ihara zeta (finite labelled spectral form)" atlas176Labelled_iff,
fromIff "Graph cycle and cut spaces (finite labelled spectral form)" atlas177Labelled_iff,
fromIff "Electrical networks (finite labelled spectral form)" atlas178Labelled_iff,
fromIff "Hypergraph spectra (finite labelled spectral form)" atlas179Labelled_iff,
fromIff "Simplicial Laplacians (finite labelled spectral form)" atlas180Labelled_iff,
fromIff "Cellular sheaf Laplacians (finite labelled spectral form)" atlas181Labelled_iff,
fromIff "Incidence algebras of finite posets (finite labelled spectral form)" atlas182Labelled_iff,
fromIff "Bipartite matchings and assignment (finite labelled spectral form)" atlas183Labelled_iff,
fromIff "Linear discrete dynamics (finite labelled spectral form)" atlas184Labelled_iff,
fromIff "Continuous linear dynamics (finite labelled spectral form)" atlas185Labelled_iff,
fromIff "Floquet theory (finite labelled spectral form)" atlas186Labelled_iff,
fromIff "Oseledets theory (finite labelled spectral form)" atlas187Labelled_iff,
fromIff "Koopman operators (finite labelled spectral form)" atlas188Labelled_iff,
fromIff "Transfer operators (finite labelled spectral form)" atlas189Labelled_iff,
fromIff "Dynamical zeta functions (finite labelled spectral form)" atlas190Labelled_iff,
fromIff "Thermodynamic formalism (finite labelled spectral form)" atlas191Labelled_iff,
fromIff "Multifractal analysis (finite labelled spectral form)" atlas192Labelled_iff,
fromIff "Control theory (finite labelled spectral form)" atlas193Labelled_iff,
fromIff "Lyapunov stability and LMIs (finite labelled spectral form)" atlas194Labelled_iff,
fromIff "Joint spectral radius (finite labelled spectral form)" atlas195Labelled_iff,
fromIff "Laplace-Beltrami operator (finite labelled spectral form)" atlas196Labelled_iff,
fromIff "Schrodinger operators (finite labelled spectral form)" atlas197Labelled_iff,
fromIff "Dirac operators (finite labelled spectral form)" atlas198Labelled_iff,
fromIff "Elliptic boundary problems (finite labelled spectral form)" atlas199Labelled_iff,
fromIff "Steklov spectral geometry (finite labelled spectral form)" atlas200Labelled_iff,
fromIff "Wave equations (finite labelled spectral form)" atlas201Labelled_iff,
fromIff "Quantum mechanics (finite labelled spectral form)" atlas202Labelled_iff,
fromIff "Quantum statistical mechanics (finite labelled spectral form)" atlas203Labelled_iff,
fromIff "Quantum channels (finite labelled spectral form)" atlas204Labelled_iff,
fromIff "Lindblad generators (finite labelled spectral form)" atlas205Labelled_iff,
fromIff "Random matrix theory (finite labelled spectral form)" atlas206Labelled_iff,
fromIff "Transfer-matrix statistical mechanics (finite labelled spectral form)" atlas207Labelled_iff,
fromIff "Covariance matrices (finite labelled spectral form)" atlas208Labelled_iff,
fromIff "Precision matrices (finite labelled spectral form)" atlas209Labelled_iff,
fromIff "Correlation matrices (finite labelled spectral form)" atlas210Labelled_iff,
fromIff "Fisher information geometry (finite labelled spectral form)" atlas211Labelled_iff,
fromIff "Gaussian entropy (finite labelled spectral form)" atlas212Labelled_iff,
fromIff "Density operators (finite labelled spectral form)" atlas213Labelled_iff,
fromIff "Von Neumann entropy (finite labelled spectral form)" atlas214Labelled_iff,
fromIff "Markov chains (finite labelled spectral form)" atlas215Labelled_iff,
fromIff "Reversible Markov chains (finite labelled spectral form)" atlas216Labelled_iff,
fromIff "Principal component analysis (finite labelled spectral form)" atlas217Labelled_iff,
fromIff "Kernel methods and reproducing kernel Hilbert spaces (finite labelled spectral form)" atlas218Labelled_iff,
fromIff "Optimal experimental design (finite labelled spectral form)" atlas219Labelled_iff,
fromIff "Rigid symmetric monoidal categories (finite labelled spectral form)" atlas220Labelled_iff,
fromIff "Additive and abelian categories (finite labelled spectral form)" atlas221Labelled_iff,
fromIff "Stable homotopy theory (finite labelled spectral form)" atlas222Labelled_iff,
fromIff "Algebraic K0 (finite labelled spectral form)" atlas223Labelled_iff,
fromIff "Algebraic K1 (finite labelled spectral form)" atlas224Labelled_iff,
fromIff "Whitehead torsion (finite labelled spectral form)" atlas225Labelled_iff,
fromIff "Topological K-theory (finite labelled spectral form)" atlas226Labelled_iff,
fromIff "Fusion categories (finite labelled spectral form)" atlas227Labelled_iff,
fromIff "Modular tensor categories (finite labelled spectral form)" atlas228Labelled_iff,
fromIff "Quantum groups (finite labelled spectral form)" atlas229Labelled_iff,
fromIff "Hopf algebras (finite labelled spectral form)" atlas230Labelled_iff,
fromIff "Coalgebras and comodules (finite labelled spectral form)" atlas231Labelled_iff,
fromIff "Berkovich analytic geometry (finite labelled spectral form)" atlas232Labelled_iff,
fromIff "Nonarchimedean matrix analysis (finite labelled spectral form)" atlas233Labelled_iff,
fromIff "Smith normal form over a principal ideal domain (finite labelled spectral form)" atlas234Labelled_iff,
fromIff "Module length over a discrete valuation ring (finite labelled spectral form)" atlas235Labelled_iff,
fromIff "Iwasawa theory (finite labelled spectral form)" atlas236Labelled_iff,
fromIff "Differential modules and irregular connections (finite labelled spectral form)" atlas237Labelled_iff,
fromIff "Difference equations (finite labelled spectral form)" atlas238Labelled_iff,
fromIff "Filtered vector spaces (finite labelled spectral form)" atlas239Labelled_iff,
fromIff "Metric entropy and singular-value pressure (finite labelled spectral form)" atlas240Labelled_iff,
fromIff "Fractal spectral geometry (finite labelled spectral form)" atlas241Labelled_iff,
fromIff "Nonlinear Perron-Frobenius theory (finite labelled spectral form)" atlas242Labelled_iff,
fromIff "Numerical-range theory for tuples (finite labelled spectral form)" atlas243Labelled_iff]

def allRoutes : List (Route MOCIsTrue) := nativeRoutes ++ labelledRoutes

theorem all_routes_iff : AnyRoute allRoutes ↔ MOCIsTrue := by
  unfold allRoutes
  exact any_iff_of_branch "Normal complex matrices" moc_iff_complexMatrices.symm
    (List.mem_append_left labelledRoutes normal_mem_nativeRoutes)

/-- Prove one all-order route, or choose a route at every order from four on.
The choices at different orders can be independent. -/
theorem moc_iff_registered_routes :
    MOCIsTrue ↔ AnyRoute allRoutes ∨
      (AnyRoute fourRoutes ∧ AnyRoute fiveRoutes ∧
        ∀ n (hn : 6 ≤ n), AnyRoute (orderRoutes n (Nat.le_trans (by decide : 4 ≤ 6) hn))) := by
  constructor
  · intro h
    exact Or.inl (all_routes_iff.mpr h)
  · rintro (hall | ⟨hfour, hfive, hhigher⟩)
    · exact all_routes_iff.mp hall
    · exact all_iff_four_and_five_and_higher.mpr
        ⟨close_any hfour, close_any hfive, fun n hn => close_any (hhigher n hn)⟩

/-- A proof of an all-order analogy can also close either finite-order root.
The finite-order route is enough by itself; it need not prove all orders. -/
theorem four_own_or_all_routes_iff :
    (AnyRoute fourRoutes ∨ AnyRoute allRoutes) ↔ Conjecture (Fin 4) :=
  ⟨fun h => h.elim four_routes_iff.mp (fun he => all_routes_iff.mp he 4),
   fun h => Or.inl (four_routes_iff.mpr h)⟩

theorem five_own_or_all_routes_iff :
    (AnyRoute fiveRoutes ∨ AnyRoute allRoutes) ↔ Conjecture (Fin 5) :=
  ⟨fun h => h.elim five_routes_iff.mp (fun he => all_routes_iff.mp he 5),
   fun h => Or.inl (five_routes_iff.mpr h)⟩

theorem all_route_implies_exact_at {n : ℕ} (source : Route MOCIsTrue)
    (target : Route (Conjecture (Fin n))) (ht : target.isExact = true) :
    source.goal → target.goal :=
  fun h => target.reverse ht (source.close h n)

/-- Refuting a single sufficient-only route does not refute its parent.
A checked failure of the parent, however, refutes every listed route. -/
theorem not_any_iff_all_failed {P : Prop} (routes : List (Route P)) :
    (¬ AnyRoute routes) ↔ ∀ r ∈ routes, ¬ r.goal :=
  ⟨fun h r hr hp => h ⟨r, hr, hp⟩, fun h ⟨r, hr, hp⟩ => h r hr hp⟩

end ProofRoutes
end MOC
