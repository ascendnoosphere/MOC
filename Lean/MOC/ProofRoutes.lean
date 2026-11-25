import MOC.Reformulations
import MOC.NormalSupportMaximum
import MOC.OrderFourIndependent
import MOC.OrderFiveContact
import MOC.OrderFiveCommonLawObstruction
import MOC.OrderFivePairMarkers
import MOC.PrincipalCoisometry
import MOC.ReducingCommutant
import MOC.SpectralMinorDecomposition
import MOC.SaturatedContactReduction

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

def fourRoutes : List (Route (Conjecture (Fin 4))) :=
  [fromIff "Normal matrices of order four" conjecture_iff_normalConjecture.symm,
   fromIff "Real orthogonal mixers with complex spectra" conjecture_four_iff_orthogonal.symm,
   fromIff "Regular orthogonal support maximizers"
      conjecture_four_iff_regular_orthogonal_support_maxima.symm,
   fromIff "Normal sum at a support maximizer" conjecture_four_iff_exists_normal_support_maximizer.symm,
   fromIff "One-entry positive laws" (oneEntryLaw_iff 4),
   fromIff "Evaluated atlas comparison at order four" (some_labelledAt_iff 4),
   fromIff "Principal coisometry of dimension three" (conjecture_iff_principalCoisometry 3).symm,
   of_witness_iff "Exclude all regular stationary orthogonal witnesses"
      not_conjecture_four_iff_regular_stationary_orthogonal_witness,
   fromIff "Nonzero six-contact support bound" conjecture_iff_contact_saturated_bound.symm,
   sufficient "One-contact transfer AND the six-contact support test"
      (fun h : SixContactStep ∧ Reformulations.ContactForm 4 6 =>
        conjecture_of_contact_step h.1 h.2),
   fromIff "Three-anchor rank-one kernel"
      (Reformulations.conjecture_iff_three_anchor_kernel (0 : Fin 4) 1 0 (by simp)).symm]

def fiveRoutes : List (Route (Conjecture (Fin 5))) :=
  [fromIff "Normal matrices of order five" conjecture_iff_normalConjecture.symm,
   fromIff "Regular spectra and full-support mixers"
      conjecture_iff_regular_spectra_full_support.symm,
   fromIff "One-entry positive laws" (oneEntryLaw_iff 5),
   fromIff "Evaluated atlas comparison at order five" (some_labelledAt_iff 5),
   fromIff "Principal coisometry of dimension four" (conjecture_iff_principalCoisometry 4).symm,
   fromIff "Three-anchor rank-one kernel"
      (Reformulations.conjecture_iff_three_anchor_kernel (0 : Fin 5) 1 0 (by simp)).symm,
   sufficient "Order four AND existence of normal order-five maximizers"
      (fun h : Conjecture (Fin 4) ∧ NormalMaximizers 5 =>
        five_of_four_and_normalMaximizers h.1 h.2),
   fromIff "Nonzero eight-contact support bound" conjecture_iff_contact_saturated_bound.symm,
   sufficient "One-contact transfer AND the eight-contact support test"
      (fun h : EightContactStep ∧ FullSupportEightContactTest =>
        (conjecture_five_iff_fullSupportEight_of_step h.1).mpr h.2),
   sufficient "Orthogonal minor convexification AND orthogonal order five"
      (fun h : TwoOrthogonalMinorTables (Fin 5) ∧ OrthogonalConjecture (Fin 5) =>
        (conjecture_iff_orthogonal_of_minor_convexification h.1).mpr h.2)]

theorem four_routes_iff : AnyRoute fourRoutes ↔ Conjecture (Fin 4) :=
  any_iff_of_branch _ conjecture_iff_normalConjecture.symm (List.mem_cons_self ..)

theorem five_routes_iff : AnyRoute fiveRoutes ↔ Conjecture (Fin 5) :=
  any_iff_of_branch _ conjecture_iff_normalConjecture.symm (List.mem_cons_self ..)

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
   fromIff "Affine linear parts" moc_iff_affineLinearParts.symm,
   fromIff "Nonzero spectra" moc_iff_nonzeroSpectra.symm,
   fromIff "Invertible projective diagonal lifts" moc_iff_projectiveDiagonalLifts.symm,
   fromIff "Traceless Cartan spectra" tracelessCartanForm_iff,
   fromIff "Newton monomials" newtonMonomialForm_iff,
   fromIff "Constant-generator monodromy" constantMonodromyForm_iff,
   fromIff "Finite bipartite matching" bipartiteMatchingForm_iff,
   fromIff "Finite Euler determinant" finiteEulerForm_iff,
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
   fromIff "Regular spectra with scalar common commutant"
      mocIsTrue_iff_regular_scalar_common_commutant.symm,
   fromIff "All three order ranges" all_iff_four_and_five_and_higher.symm,
   sufficient "Simultaneous characteristic hull" CStar.moc_of_simultaneousCharacteristicForm,
   sufficient "Simultaneous mixed-pencil coefficients" moc_of_simultaneousMixedPencilHull]

private theorem normal_mem_nativeRoutes :
    fromIff "Normal complex matrices" moc_iff_complexMatrices.symm ∈ nativeRoutes := by
  unfold nativeRoutes
  exact List.mem_cons_self

theorem native_routes_iff : AnyRoute nativeRoutes ↔ MOCIsTrue :=
  any_iff_of_branch "Normal complex matrices" moc_iff_complexMatrices.symm normal_mem_nativeRoutes

/-- This is the evaluated spectral layer of the atlas, not a list of
unconditional native statements. Each numbered leaf uses its own checked
equivalence to unrestricted MOC. -/
opaque labelledRoutes : List (Route MOCIsTrue) :=
  [fromIff "Atlas 001 evaluated" atlas001Labelled_iff,
fromIff "Atlas 002 evaluated" atlas002Labelled_iff,
fromIff "Atlas 003 evaluated" atlas003Labelled_iff,
fromIff "Atlas 004 evaluated" atlas004Labelled_iff,
fromIff "Atlas 005 evaluated" atlas005Labelled_iff,
fromIff "Atlas 006 evaluated" atlas006Labelled_iff,
fromIff "Atlas 007 evaluated" atlas007Labelled_iff,
fromIff "Atlas 008 evaluated" atlas008Labelled_iff,
fromIff "Atlas 009 evaluated" atlas009Labelled_iff,
fromIff "Atlas 010 evaluated" atlas010Labelled_iff,
fromIff "Atlas 011 evaluated" atlas011Labelled_iff,
fromIff "Atlas 012 evaluated" atlas012Labelled_iff,
fromIff "Atlas 013 evaluated" atlas013Labelled_iff,
fromIff "Atlas 014 evaluated" atlas014Labelled_iff,
fromIff "Atlas 015 evaluated" atlas015Labelled_iff,
fromIff "Atlas 016 evaluated" atlas016Labelled_iff,
fromIff "Atlas 017 evaluated" atlas017Labelled_iff,
fromIff "Atlas 018 evaluated" atlas018Labelled_iff,
fromIff "Atlas 019 evaluated" atlas019Labelled_iff,
fromIff "Atlas 020 evaluated" atlas020Labelled_iff,
fromIff "Atlas 021 evaluated" atlas021Labelled_iff,
fromIff "Atlas 022 evaluated" atlas022Labelled_iff,
fromIff "Atlas 023 evaluated" atlas023Labelled_iff,
fromIff "Atlas 024 evaluated" atlas024Labelled_iff,
fromIff "Atlas 025 evaluated" atlas025Labelled_iff,
fromIff "Atlas 026 evaluated" atlas026Labelled_iff,
fromIff "Atlas 027 evaluated" atlas027Labelled_iff,
fromIff "Atlas 028 evaluated" atlas028Labelled_iff,
fromIff "Atlas 029 evaluated" atlas029Labelled_iff,
fromIff "Atlas 030 evaluated" atlas030Labelled_iff,
fromIff "Atlas 031 evaluated" atlas031Labelled_iff,
fromIff "Atlas 032 evaluated" atlas032Labelled_iff,
fromIff "Atlas 033 evaluated" atlas033Labelled_iff,
fromIff "Atlas 034 evaluated" atlas034Labelled_iff,
fromIff "Atlas 035 evaluated" atlas035Labelled_iff,
fromIff "Atlas 036 evaluated" atlas036Labelled_iff,
fromIff "Atlas 037 evaluated" atlas037Labelled_iff,
fromIff "Atlas 038 evaluated" atlas038Labelled_iff,
fromIff "Atlas 039 evaluated" atlas039Labelled_iff,
fromIff "Atlas 040 evaluated" atlas040Labelled_iff,
fromIff "Atlas 041 evaluated" atlas041Labelled_iff,
fromIff "Atlas 042 evaluated" atlas042Labelled_iff,
fromIff "Atlas 043 evaluated" atlas043Labelled_iff,
fromIff "Atlas 044 evaluated" atlas044Labelled_iff,
fromIff "Atlas 045 evaluated" atlas045Labelled_iff,
fromIff "Atlas 046 evaluated" atlas046Labelled_iff,
fromIff "Atlas 047 evaluated" atlas047Labelled_iff,
fromIff "Atlas 048 evaluated" atlas048Labelled_iff,
fromIff "Atlas 049 evaluated" atlas049Labelled_iff,
fromIff "Atlas 050 evaluated" atlas050Labelled_iff,
fromIff "Atlas 051 evaluated" atlas051Labelled_iff,
fromIff "Atlas 052 evaluated" atlas052Labelled_iff,
fromIff "Atlas 053 evaluated" atlas053Labelled_iff,
fromIff "Atlas 054 evaluated" atlas054Labelled_iff,
fromIff "Atlas 055 evaluated" atlas055Labelled_iff,
fromIff "Atlas 056 evaluated" atlas056Labelled_iff,
fromIff "Atlas 057 evaluated" atlas057Labelled_iff,
fromIff "Atlas 058 evaluated" atlas058Labelled_iff,
fromIff "Atlas 059 evaluated" atlas059Labelled_iff,
fromIff "Atlas 060 evaluated" atlas060Labelled_iff,
fromIff "Atlas 061 evaluated" atlas061Labelled_iff,
fromIff "Atlas 062 evaluated" atlas062Labelled_iff,
fromIff "Atlas 063 evaluated" atlas063Labelled_iff,
fromIff "Atlas 064 evaluated" atlas064Labelled_iff,
fromIff "Atlas 065 evaluated" atlas065Labelled_iff,
fromIff "Atlas 066 evaluated" atlas066Labelled_iff,
fromIff "Atlas 067 evaluated" atlas067Labelled_iff,
fromIff "Atlas 068 evaluated" atlas068Labelled_iff,
fromIff "Atlas 069 evaluated" atlas069Labelled_iff,
fromIff "Atlas 070 evaluated" atlas070Labelled_iff,
fromIff "Atlas 071 evaluated" atlas071Labelled_iff,
fromIff "Atlas 072 evaluated" atlas072Labelled_iff,
fromIff "Atlas 073 evaluated" atlas073Labelled_iff,
fromIff "Atlas 074 evaluated" atlas074Labelled_iff,
fromIff "Atlas 075 evaluated" atlas075Labelled_iff,
fromIff "Atlas 076 evaluated" atlas076Labelled_iff,
fromIff "Atlas 077 evaluated" atlas077Labelled_iff,
fromIff "Atlas 078 evaluated" atlas078Labelled_iff,
fromIff "Atlas 079 evaluated" atlas079Labelled_iff,
fromIff "Atlas 080 evaluated" atlas080Labelled_iff,
fromIff "Atlas 081 evaluated" atlas081Labelled_iff,
fromIff "Atlas 082 evaluated" atlas082Labelled_iff,
fromIff "Atlas 083 evaluated" atlas083Labelled_iff,
fromIff "Atlas 084 evaluated" atlas084Labelled_iff,
fromIff "Atlas 085 evaluated" atlas085Labelled_iff,
fromIff "Atlas 086 evaluated" atlas086Labelled_iff,
fromIff "Atlas 087 evaluated" atlas087Labelled_iff,
fromIff "Atlas 088 evaluated" atlas088Labelled_iff,
fromIff "Atlas 089 evaluated" atlas089Labelled_iff,
fromIff "Atlas 090 evaluated" atlas090Labelled_iff,
fromIff "Atlas 091 evaluated" atlas091Labelled_iff,
fromIff "Atlas 092 evaluated" atlas092Labelled_iff,
fromIff "Atlas 093 evaluated" atlas093Labelled_iff,
fromIff "Atlas 094 evaluated" atlas094Labelled_iff,
fromIff "Atlas 095 evaluated" atlas095Labelled_iff,
fromIff "Atlas 096 evaluated" atlas096Labelled_iff,
fromIff "Atlas 097 evaluated" atlas097Labelled_iff,
fromIff "Atlas 098 evaluated" atlas098Labelled_iff,
fromIff "Atlas 099 evaluated" atlas099Labelled_iff,
fromIff "Atlas 100 evaluated" atlas100Labelled_iff,
fromIff "Atlas 101 evaluated" atlas101Labelled_iff,
fromIff "Atlas 102 evaluated" atlas102Labelled_iff,
fromIff "Atlas 103 evaluated" atlas103Labelled_iff,
fromIff "Atlas 104 evaluated" atlas104Labelled_iff,
fromIff "Atlas 105 evaluated" atlas105Labelled_iff,
fromIff "Atlas 106 evaluated" atlas106Labelled_iff,
fromIff "Atlas 107 evaluated" atlas107Labelled_iff,
fromIff "Atlas 108 evaluated" atlas108Labelled_iff,
fromIff "Atlas 109 evaluated" atlas109Labelled_iff,
fromIff "Atlas 110 evaluated" atlas110Labelled_iff,
fromIff "Atlas 111 evaluated" atlas111Labelled_iff,
fromIff "Atlas 112 evaluated" atlas112Labelled_iff,
fromIff "Atlas 113 evaluated" atlas113Labelled_iff,
fromIff "Atlas 114 evaluated" atlas114Labelled_iff,
fromIff "Atlas 115 evaluated" atlas115Labelled_iff,
fromIff "Atlas 116 evaluated" atlas116Labelled_iff,
fromIff "Atlas 117 evaluated" atlas117Labelled_iff,
fromIff "Atlas 118 evaluated" atlas118Labelled_iff,
fromIff "Atlas 119 evaluated" atlas119Labelled_iff,
fromIff "Atlas 120 evaluated" atlas120Labelled_iff,
fromIff "Atlas 121 evaluated" atlas121Labelled_iff,
fromIff "Atlas 122 evaluated" atlas122Labelled_iff,
fromIff "Atlas 123 evaluated" atlas123Labelled_iff,
fromIff "Atlas 124 evaluated" atlas124Labelled_iff,
fromIff "Atlas 125 evaluated" atlas125Labelled_iff,
fromIff "Atlas 126 evaluated" atlas126Labelled_iff,
fromIff "Atlas 127 evaluated" atlas127Labelled_iff,
fromIff "Atlas 128 evaluated" atlas128Labelled_iff,
fromIff "Atlas 129 evaluated" atlas129Labelled_iff,
fromIff "Atlas 130 evaluated" atlas130Labelled_iff,
fromIff "Atlas 131 evaluated" atlas131Labelled_iff,
fromIff "Atlas 132 evaluated" atlas132Labelled_iff,
fromIff "Atlas 133 evaluated" atlas133Labelled_iff,
fromIff "Atlas 134 evaluated" atlas134Labelled_iff,
fromIff "Atlas 135 evaluated" atlas135Labelled_iff,
fromIff "Atlas 136 evaluated" atlas136Labelled_iff,
fromIff "Atlas 137 evaluated" atlas137Labelled_iff,
fromIff "Atlas 138 evaluated" atlas138Labelled_iff,
fromIff "Atlas 139 evaluated" atlas139Labelled_iff,
fromIff "Atlas 140 evaluated" atlas140Labelled_iff,
fromIff "Atlas 141 evaluated" atlas141Labelled_iff,
fromIff "Atlas 142 evaluated" atlas142Labelled_iff,
fromIff "Atlas 143 evaluated" atlas143Labelled_iff,
fromIff "Atlas 144 evaluated" atlas144Labelled_iff,
fromIff "Atlas 145 evaluated" atlas145Labelled_iff,
fromIff "Atlas 146 evaluated" atlas146Labelled_iff,
fromIff "Atlas 147 evaluated" atlas147Labelled_iff,
fromIff "Atlas 148 evaluated" atlas148Labelled_iff,
fromIff "Atlas 149 evaluated" atlas149Labelled_iff,
fromIff "Atlas 150 evaluated" atlas150Labelled_iff,
fromIff "Atlas 151 evaluated" atlas151Labelled_iff,
fromIff "Atlas 152 evaluated" atlas152Labelled_iff,
fromIff "Atlas 153 evaluated" atlas153Labelled_iff,
fromIff "Atlas 154 evaluated" atlas154Labelled_iff,
fromIff "Atlas 155 evaluated" atlas155Labelled_iff,
fromIff "Atlas 156 evaluated" atlas156Labelled_iff,
fromIff "Atlas 157 evaluated" atlas157Labelled_iff,
fromIff "Atlas 158 evaluated" atlas158Labelled_iff,
fromIff "Atlas 159 evaluated" atlas159Labelled_iff,
fromIff "Atlas 160 evaluated" atlas160Labelled_iff,
fromIff "Atlas 161 evaluated" atlas161Labelled_iff,
fromIff "Atlas 162 evaluated" atlas162Labelled_iff,
fromIff "Atlas 163 evaluated" atlas163Labelled_iff,
fromIff "Atlas 164 evaluated" atlas164Labelled_iff,
fromIff "Atlas 165 evaluated" atlas165Labelled_iff,
fromIff "Atlas 166 evaluated" atlas166Labelled_iff,
fromIff "Atlas 167 evaluated" atlas167Labelled_iff,
fromIff "Atlas 168 evaluated" atlas168Labelled_iff,
fromIff "Atlas 169 evaluated" atlas169Labelled_iff,
fromIff "Atlas 170 evaluated" atlas170Labelled_iff,
fromIff "Atlas 171 evaluated" atlas171Labelled_iff,
fromIff "Atlas 172 evaluated" atlas172Labelled_iff,
fromIff "Atlas 173 evaluated" atlas173Labelled_iff,
fromIff "Atlas 174 evaluated" atlas174Labelled_iff,
fromIff "Atlas 175 evaluated" atlas175Labelled_iff,
fromIff "Atlas 176 evaluated" atlas176Labelled_iff,
fromIff "Atlas 177 evaluated" atlas177Labelled_iff,
fromIff "Atlas 178 evaluated" atlas178Labelled_iff,
fromIff "Atlas 179 evaluated" atlas179Labelled_iff,
fromIff "Atlas 180 evaluated" atlas180Labelled_iff,
fromIff "Atlas 181 evaluated" atlas181Labelled_iff,
fromIff "Atlas 182 evaluated" atlas182Labelled_iff,
fromIff "Atlas 183 evaluated" atlas183Labelled_iff,
fromIff "Atlas 184 evaluated" atlas184Labelled_iff,
fromIff "Atlas 185 evaluated" atlas185Labelled_iff,
fromIff "Atlas 186 evaluated" atlas186Labelled_iff,
fromIff "Atlas 187 evaluated" atlas187Labelled_iff,
fromIff "Atlas 188 evaluated" atlas188Labelled_iff,
fromIff "Atlas 189 evaluated" atlas189Labelled_iff,
fromIff "Atlas 190 evaluated" atlas190Labelled_iff,
fromIff "Atlas 191 evaluated" atlas191Labelled_iff,
fromIff "Atlas 192 evaluated" atlas192Labelled_iff,
fromIff "Atlas 193 evaluated" atlas193Labelled_iff,
fromIff "Atlas 194 evaluated" atlas194Labelled_iff,
fromIff "Atlas 195 evaluated" atlas195Labelled_iff,
fromIff "Atlas 196 evaluated" atlas196Labelled_iff,
fromIff "Atlas 197 evaluated" atlas197Labelled_iff,
fromIff "Atlas 198 evaluated" atlas198Labelled_iff,
fromIff "Atlas 199 evaluated" atlas199Labelled_iff,
fromIff "Atlas 200 evaluated" atlas200Labelled_iff,
fromIff "Atlas 201 evaluated" atlas201Labelled_iff,
fromIff "Atlas 202 evaluated" atlas202Labelled_iff,
fromIff "Atlas 203 evaluated" atlas203Labelled_iff,
fromIff "Atlas 204 evaluated" atlas204Labelled_iff,
fromIff "Atlas 205 evaluated" atlas205Labelled_iff,
fromIff "Atlas 206 evaluated" atlas206Labelled_iff,
fromIff "Atlas 207 evaluated" atlas207Labelled_iff,
fromIff "Atlas 208 evaluated" atlas208Labelled_iff,
fromIff "Atlas 209 evaluated" atlas209Labelled_iff,
fromIff "Atlas 210 evaluated" atlas210Labelled_iff,
fromIff "Atlas 211 evaluated" atlas211Labelled_iff,
fromIff "Atlas 212 evaluated" atlas212Labelled_iff,
fromIff "Atlas 213 evaluated" atlas213Labelled_iff,
fromIff "Atlas 214 evaluated" atlas214Labelled_iff,
fromIff "Atlas 215 evaluated" atlas215Labelled_iff,
fromIff "Atlas 216 evaluated" atlas216Labelled_iff,
fromIff "Atlas 217 evaluated" atlas217Labelled_iff,
fromIff "Atlas 218 evaluated" atlas218Labelled_iff,
fromIff "Atlas 219 evaluated" atlas219Labelled_iff,
fromIff "Atlas 220 evaluated" atlas220Labelled_iff,
fromIff "Atlas 221 evaluated" atlas221Labelled_iff,
fromIff "Atlas 222 evaluated" atlas222Labelled_iff,
fromIff "Atlas 223 evaluated" atlas223Labelled_iff,
fromIff "Atlas 224 evaluated" atlas224Labelled_iff,
fromIff "Atlas 225 evaluated" atlas225Labelled_iff,
fromIff "Atlas 226 evaluated" atlas226Labelled_iff,
fromIff "Atlas 227 evaluated" atlas227Labelled_iff,
fromIff "Atlas 228 evaluated" atlas228Labelled_iff,
fromIff "Atlas 229 evaluated" atlas229Labelled_iff,
fromIff "Atlas 230 evaluated" atlas230Labelled_iff,
fromIff "Atlas 231 evaluated" atlas231Labelled_iff,
fromIff "Atlas 232 evaluated" atlas232Labelled_iff,
fromIff "Atlas 233 evaluated" atlas233Labelled_iff,
fromIff "Atlas 234 evaluated" atlas234Labelled_iff,
fromIff "Atlas 235 evaluated" atlas235Labelled_iff,
fromIff "Atlas 236 evaluated" atlas236Labelled_iff,
fromIff "Atlas 237 evaluated" atlas237Labelled_iff,
fromIff "Atlas 238 evaluated" atlas238Labelled_iff,
fromIff "Atlas 239 evaluated" atlas239Labelled_iff,
fromIff "Atlas 240 evaluated" atlas240Labelled_iff,
fromIff "Atlas 241 evaluated" atlas241Labelled_iff,
fromIff "Atlas 242 evaluated" atlas242Labelled_iff,
fromIff "Atlas 243 evaluated" atlas243Labelled_iff]

def allRoutes : List (Route MOCIsTrue) := nativeRoutes ++ labelledRoutes

theorem all_routes_iff : AnyRoute allRoutes ↔ MOCIsTrue := by
  unfold allRoutes
  exact any_iff_of_branch "Normal complex matrices" moc_iff_complexMatrices.symm
    (List.mem_append_left labelledRoutes normal_mem_nativeRoutes)

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
