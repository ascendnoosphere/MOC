/-!
# Lean coverage for matrix, operator, and geometric comparisons

Each row gives the scope of a comparison on the stated mathematical objects.
The identifier matches the corresponding labelled spectral form in
`FirstAtlas.lean`. An equivalence gives implications in both directions.
The status column distinguishes proved comparisons, restrictions, and gaps.

A dash in the declaration column means that the native step is not
formalized. For arrows to full MOC, see `NativeAudit.lean`.

ID | Subject | Status | Lean declaration or gap | Exact scope
001 | Complex matrices | exact native iff | FirstMatrix.moc_iff_complexMatrices | Actual normal matrix determinant with charpoly roots and arbitrary unitary rotation.
002 | Normal matrices | exact native iff | FirstMatrix.moc_iff_normalFrames; Normal.conjecture_iff_normalConjecture | Actual normal matrices and orthonormal eigenframes.
003 | Hermitian matrices | existing native checked | FirstHermitian.hermitianMatrixHull; FirstHermitian.hermitianSpectralHull | Actual Hermitian matrix hull; output real and equivalent to interval form.
004 | Positive definite matrices | existing native checked | FirstHermitian.positiveDefiniteMatrixHull; FirstHermitian.positiveDefiniteSpectralHull | Positive-definite specialization; scalar positivity is also used in native log-det theorem 046.
005 | Unitary matrices | existing native checked | FirstUnitary.unitaryMatrixHull; FirstUnitary.unitarySpectralHull | Actual unitary matrices with arbitrary relative unitary position and their characteristic roots.
006 | Nonnormal matrices | exact native iff | FirstMatrix.moc_iff_nonnormalSpectralRepresentatives | Actual charpoly roots and normal diagonal representatives, not nonnormal sums.
007 | Rectangular maps | existing native checked | FirstHermitian.rectangularAbsoluteHull | Actual PSD square roots of rectangular Gram matrices.
008 | Commuting normal tuple | exact native spectral iff | FirstMatrix.moc_iff_commutingTupleProjections | Joint spectral coordinates and single scalar direction. No simultaneous law is claimed.
009 | Regular matrix pencils | exact native iff | FirstMatrix.moc_iff_normalizedPencils | Actual normalized inverse products; identity denominators recover all normal matrices.
010 | Monic matrix polynomials | new exact native iff | NativeFirstAPolynomial.moc_iff_nativeMonicMatrixPolynomialRoots | Actual monic matrix-polynomial determinant roots, with the diagonal root realization explicitly permitted in the source. No blanket companion normality.
011 | Real skew-symmetric matrices | restricted native spectral theorem | FirstHermitian.imaginarySpectralHull | All purely imaginary spectra with complex unitary mixing; not a Pfaffian identity or an independent formalization of skew-matrix spectral classification.
012 | Commutative-ring matrices | exact native iff | FirstMatrix.moc_iff_commutativeRingMatrices | Actual entrywise complex realization of commutative-ring matrices.
013 | Exterior power | exact native spectral iff | FirstStructured.moc_iff_exteriorSpectrum | Actual indexed subset monomials in wedge eigenbasis; exterior operator compatibility not independently formalized.
014 | Top exterior power | new exact native iff | NativeFirstAPolynomial.moc_iff_nativeTopExteriorHull | Top alternating coordinate of the actual sum via Basis.det_comp.
015 | Symmetric power | exact native spectral iff | FirstStructured.moc_iff_symmetricSpectrum | Actual symmetric multi-index monomials; operator compatibility not independently formalized.
016 | Tensor product | exact native spectral iff | FirstStructured.moc_iff_tensorSpectrum | All pairwise products on the actual tensor eigenvalue index; no independent Kronecker matrix compatibility proof.
017 | Direct sum | exact native spectral iff | FirstStructured.moc_iff_directSumSpectrum | Actual concatenated eigenvalue lists with arbitrary mixing between summand coordinates.
018 | Kronecker sum | exact native spectral iff | FirstStructured.moc_iff_kroneckerSumSpectrum | Actual Kronecker-sum eigenvalue sums; no independent Kronecker matrix compatibility proof.
019 | Endomorphism algebra, adjoint action | existing native spectral forward and selected iff | FirstStructured.adjointSpectrum_of_moc; FirstStructured.moc_iff_selectedAdjointSpectrum | Full eigenvalue differences receive forward link only; selecting reference-column matrix units gives iff.
020 | Conjugation action | existing native spectral forward and selected iff | FirstStructured.conjugationSpectrum_of_moc; FirstGeometric.moc_iff_selectedConjugationSpectrum | Full ratio family is one-way; selected reference-column form admits opposite scalar shifts before ratios.
021 | Tensor algebraic eigenvalues | existing native counterexample | FirstResultant.binaryCubic_additiveResultantCounterexample | Binary cubic resultant specialization 64 versus {0}; no generic multivariate resultant engine.
022 | Tensor Z-eigenvalues | existing native counterexample | FirstTensorStationary.binaryQuartic_exampleZValues; FirstTensorStationary.binaryQuartic_product_not_mem_hull | Exact native Z-values and a symbolic uniform rank-one bound.
023 | GKZ hyperdeterminant | existing native counterexample | FirstHyperdeterminant.cayleyDiagonalOrbitHull_false | Actual first-two-mode orbit in 2×2×2 gives 9 outside {4}; no general dual Segre theory.
024 | Gram matrices | existing native checked | FirstHermitian.gramMatrixHull | Actual rectangular Gram matrices and squared singular values.
025 | Finite associative unital algebra | new exact native iff | NativeFirstAAlgebra.moc_iff_nativeLeftRegularAlgebra | Actual left regular maps; split scalar coordinate algebra gives reverse.
026 | Finite commutative algebra | new native split theorem | NativeFirstAAlgebra.splitCoordinateAlgebraNorm_mem_hull | Actual determinant of multiplication on split algebra. General Artinian local factors require local character multiplicity theory.
027 | Central simple algebra | new exact native iff | NativeFirstARepresentations.moc_iff_nativeSplitScalarExtension | Actual tensor scalar extension and splitting algebra equivalence, for a family stronger than central simple inputs.
028 | Quaternion algebra | new native checked | NativeFirstAQuaternion.nativeUnitQuaternionNormHull | Actual quaternion multiplication, star inversion at unit norm, and exact two norm endpoints.
029 | Quaternionic matrices | native transport not checked | FirstMatrix.moc_iff_complexMatrices | Quaternionic adjoint-preserving complex block representation must be instantiated and its spectral normalization checked.
030 | Division-ring matrices | new exact native iff | NativeFirstARepresentations.moc_iff_nativeDivisionBlockHull | Actual entrywise block extension of faithful ring representation; scalar blocks give reverse.
031 | Octonion algebra | native metric reduction only | NativeFirstAQuaternion.nativeScalarImaginaryNormBounds | Actual norm-bound argument in arbitrary real inner-product imaginary coordinates. Octonion algebra and automorphism preservation not formalized.
032 | Clifford algebra | native gap |  | Finite representation argument is symbolic via 051, but an actual Clifford target requires compiled quadratic-form isometry dependencies; no spinor/regular reverse follows automatically.
033 | Finite group algebra | native gap |  | Need actual complex group algebra star-compatible regular matrix map and cyclic Fourier construction, not an arbitrary spectral relabelling.
034 | Frobenius algebra | new exact native iff | NativeFirstAAlgebra.moc_iff_nativeFrobeniusAlgebra | Actual bilinear nondegeneracy from the Frobenius functional; construct coordinate sum in reverse.
035 | Polynomial quotient | exact native theorem | NativeFirstABaseChange.polynomialQuotientNorm_eq_prod_eval; NativeFirstABaseChange.polynomialQuotientNorm_mem_hull | Actual AdjoinRoot quotient; multiplication norm is the product of evaluations at all roots counted with multiplicity, so the identity matching is attained.
036 | Finite projective module | new native forward | NativeFirstABaseChange.nativeProjectiveFiberHull_of_moc | Actual tensor scalar extension of endomorphisms. Free-fiber reverse is mathematically available but not separately checked here.
037 | Euclidean Jordan algebra | native gap |  | A general Euclidean Jordan-algebra model with Jordan-frame spectrum and automorphisms is not provided here; 038/039/042 are separate.
038 | Real symmetric Jordan algebra | native specialization only | FirstHermitian.hermitianMatrixHull; Realification.isUnitary_ofReal_orthogonal | Complexification route available. Explicit proof identifying real spectral lists under complexification and real matrix det not added.
039 | Complex Hermitian Jordan algebra | existing native checked | FirstHermitian.hermitianMatrixHull | Complex Hermitian Jordan determinant is the actual ordinary determinant of the Hermitian sum.
040 | Quaternionic Hermitian Jordan algebra | native target not checked | — | Real right eigenvalues of quaternionic Hermitian sum and signed Moore determinant need their own hull theorem. Taking square roots of the complex determinant hull is not an implication.
041 | Albert algebra | native gap |  | Need an Albert algebra model and determinant spectral law; rank-three ordinary matrix results do not justify the exceptional cubic norm.
042 | Spin factor | existing native checked | FirstSpinFactor.spinFactorBounds; FirstSpinFactor.spinEndpoints | Exact rank-two endpoints with Cauchy–Schwarz.
043 | Symmetric cones | matrix specialization only | FirstHermitian.positiveDefiniteSpectralHull | No general Euclidean Jordan cone or unrestricted Jordan automorphism hull theorem supplied.
044 | Hyperbolic polynomial | native rank-two specialization | NativeLinksAQuadratic.hyperbolicQuadratic_matching_bounds | Actual normalized quadratic polynomial, real roots and structural inequalities. Higher-degree general hyperbolic claim not inferred.
045 | Elementary symmetric cones | native gap |  | Higher-degree elementary-symmetric directional roots and homogeneous normalization e_k(1) require separate algebra; product case not enough.
046 | Determinant barrier theory | new native checked | NativeFirstAHermitian.nativeDeterminantBarrier | Actual positive Hermitian sum; positive determinant bracket and decreasing log yield true endpoint comparisons.
047 | Spectral convex analysis | new native checked | NativeFirstAHermitian.nativeHermitianSumEigenvalueHull | Actual eigenvalues of Hermitian sum; order irrelevant to product.
048 | Mixed discriminants | native pointwise iff and boundary coefficients | FirstStructured.moc_iff_pointwiseMixedDiscriminant; NativeLinksA.mixedPencil_boundary_coeff_hulls | Simultaneous coefficient form is separate and stronger; interior coefficient statement not asserted.
049 | Banach-space operators | new native forward | NativeFirstAOperators.nativeInvariantBanachHull_of_moc | Actual bounded maps with invariant subspace. Matrix reverse via full finite Banach space is not separately mechanized.
050 | Hilbert-space operators | new finite restriction iff | NativeFirstAFredholm.moc_iff_nativeFiniteFredholmHull | Finite shifted Fredholm determinants exact; no infinite trace-class approximation or closed-hull theorem.
051 | Unital Banach algebra | new native algebraic iff | NativeFirstARepresentations.moc_iff_nativeComplexAlgebraRepresentation | Actual unital complex algebra homs, stronger than Banach continuous source. Reverse by matrix identity representation.
052 | Commutative C-star algebra C(X) | native coupling attainment and bounded-extrema link | NativeLinksACoupling.commutativeLogDet_mem_couplings; NativeLinksACoupling.commutativeLogDet_bounds | Actual joint law and Bochner integral. Compact positive continuous data imply boundedness mathematically; compact support-to-uniform integrability proof not added.
053 | Unital C-star algebra | new native algebraic iff | NativeFirstARepresentations.moc_iff_nativeStarAlgebraRepresentation | Actual adjoint-preserving source algebra and source unitary, stronger than C-star normed setting.
054 | Normal C-star element | existing finite spectral calculus iff | CStar.functionalCalculusForm_iff | Actual functions on represented eigenvalues; abstract C-star continuous functional calculus and representation compatibility not independently proved.
055 | Finite von Neumann algebra | native gap |  | No finite von Neumann FK determinant operator-existence, continuity or positive trace optimization supplied. Matrix complex hull does not imply arbitrary trace-log transport.
056 | Type II1 factor | native gap |  | Need diffuse factor trace/projection transport and type-II₁ FK log determinant; integer matrix coupling theorem has different scope.
057 | Semifinite von Neumann algebra | native gap |  | Need actual semifinite finite-trace corner and trace renormalization, not finite matrices relabelled as the ambient algebra.
058 | Group von Neumann algebra | native gap |  | Need von Neumann convolution algebra with faithful trace and operator-valued log calculus. Finite-group matrix determinant would not prove infinite trace-log result.
059 | Free probability | native gap |  | Need additive free convolution law and logarithmic coupling extremum; free independence gives no unconditional reverse link.
060 | Calkin algebra | native gap |  | After an actual Calkin matrix-subalgebra isomorphism the matrix step follows, but constructing the faithful quotient amplification and its compactness obstruction is not formalized.
061 | Compact operators | new native forward | NativeFirstAOperators.nativeCompactCompression_of_moc | Actual compact normal Hilbert operators and orthogonal compression; no assertion that arbitrary compressions are normal.
062 | Trace-class operators | new finite restriction iff | NativeFirstAFredholm.moc_iff_nativeFiniteFredholmHull | Actual finite shifted determinant. Infinite trace-ideal continuity and approximation are separate.
063 | Hilbert-Schmidt operators | new finite restriction iff | NativeFirstAFredholm.moc_iff_nativeFiniteRegularizedTwoHull | Actual trace correction cancels one nonzero exponential common to all vertices; no Hilbert–Schmidt limit claimed.
064 | Schatten classes | new finite order-two iff; finite order-three counterexample | NativeFirstAFredholm.moc_iff_nativeFiniteRegularizedTwoHull; NativeLinksASchatten.finiteSchattenThreeHull_false | Finite p=3 failure by symbolic optimization. Infinite padded hull requires separate control of padded matchings.
065 | Integral operators | new finite atomic restriction iff | NativeFirstAAtomicKernels.moc_iff_nativeFiniteAtomicKernelHull | Actual finite normalized kernel on positive atom masses and Fredholm value in chosen normal eigenbases. No trace-class limit.
066 | Elliptic operators on closed manifolds | native finite spectral reduction only | FirstHermitian.positiveDefiniteSpectralHull | Selected positive modes satisfy the finite shifted positive matrix comparison. No actual elliptic compact resolvent or eigenfunction API used.
067 | Pseudodifferential calculus | native gap |  | Normal matrix-valued symbols give the ordinary matrix step. Actual principal-symbol calculus and realizability by order-zero multiplication on a bundle are not formalized.
068 | Spectral triples | checked-native | MOC.Reformulations.NativeFirstB.diracBlockHull | Actual chosen self-adjoint finite Dirac blocks with signed roots; no zeta-pole identification.
069 | Dixmier trace theory | checked-native | MOC.Reformulations.NativeFirstB.shiftedSingularValueHull | Exact finite shifted singular-value determinant; no generalized-limit substitution.
070 | De la Harpe-Skandalis determinant | checked-native-iff | MOC.Reformulations.determinantPathForm_iff | Actual piecewise smooth path integral; construction for all invertible endpoints and a separate symbolic singular-sum theorem.
071 | Perturbation determinants | finite-restriction | MOC.Reformulations.NativeFirstB.finitePerturbationForm_iff | Exact finite relative determinant; trace-class Fredholm and closed infinite hull not formalized.
072 | Scattering theory | checked-native | MOC.Reformulations.NativeFirstB.unitaryPhaseOperatorHull | Actual finite unit-circle operator spectra; no resonance-pole substitution.
073 | Chain complexes | checked-native-iff | MOC.Reformulations.NativeFirstB.chainTermForm_iff | Actual Mathlib chain endomorphisms, converse via concentrated complex.
074 | Singular homology | checked-native | MOC.Reformulations.NativeFirstB.singularHomologyHull | Actual Mathlib singular homology and continuous self-maps; MOC implication.
075 | Singular cohomology | finite-restriction | MOC.Reformulations.NativeFirstB.singularDualHull | Actual contravariant linear dual of singular homology map; comparison with cochain model not formalized.
076 | Simplicial homology | checked-native | MOC.Reformulations.NativeFirstB.simplicialLaplacianHull | Actual chain Laplacian formula in selected simplex basis; zero modes retained.
077 | Cellular homology | finite-restriction | MOC.Reformulations.NativeFirstB.chainTermForm_iff | Applies to actual chain maps once cellular chains/maps constructed; no CW cellular functor.
078 | De Rham cohomology | native-open | No de Rham cohomology pullback construction in this pass | Requires the induced maps on harmonic/de Rham classes, not on all forms.
079 | Dolbeault cohomology | finite-restriction | MOC.Reformulations.NativeLinksB.gaussianSpectrumForm_iff (auditor) | Concrete Gaussian scalar class, not construction of Dolbeault pullbacks on all compact complex manifolds.
080 | Hodge theory | checked-native | MOC.Reformulations.NativeFirstB.hodgeWindowHull | Hermitian compression in the chosen finite Hodge windows; no infinite/zeta determinant.
081 | Intersection homology | native-open | No intersection chain and perversity functor in this pass | Need functorial maps on specified intersection homology.
082 | Group homology | finite-restriction | MOC.Reformulations.NativeFirstB.groupCoinvariantHull | Degree-zero coinvariant quotient only; higher group homology not supplied.
083 | Group cohomology | checked-native | MOC.Reformulations.NativeFirstB.groupCohomologyCoefficientHull | Actual Mathlib group cohomology for equivariant coefficient endomorphisms; arbitrary compatible group maps not treated.
084 | Sheaf cohomology | finite-restriction | MOC.Reformulations.NativeFirstB.sheafSectionHull | Actual map on sections in degree zero; derived complex-linear higher cohomology not supplied.
085 | Hypercohomology | finite-restriction | MOC.Reformulations.NativeFirstB.gradedOperatorDeterminantLine_of_moc | Actual finite degree operators and inverse-factor hull; no hypercohomology functor construction.
086 | Hochschild homology | finite-restriction | MOC.Reformulations.NativeFirstB.degreeZeroHochschildHull | Actual commutator-quotient endomorphism in degree zero only.
087 | Hochschild cohomology | finite-restriction | MOC.Reformulations.NativeFirstB.degreeZeroHochschildCohomologyHull | Actual automorphism action on the center in degree zero only.
088 | Cyclic homology | finite-restriction | MOC.Reformulations.NativeFirstB.degreeZeroHochschildHull | Degree-zero cyclic quotient by commutator span; higher cyclic complexes not formalized.
089 | Equivariant cohomology | finite-restriction | MOC.Reformulations.NativeFirstB.equivariantSpecializationHull | Actual ring-character specialization of selected finite free matrices; equivariant cohomology module construction is outside this theorem.
090 | L2-homology | finite-restriction | MOC.Reformulations.NativeFirstB.finiteNormalizedPositiveDeterminantBounds | Normalized positive finite-trace determinant and permutation-coupling witnesses; general von Neumann trace and spectral measures not treated.
091 | Persistent homology | checked-native | MOC.Reformulations.NativeFirstB.barcodeLifetimeHull | Actual finite nondegenerate intervals and lifetime operators.
092 | Spectral sequences | checked-native | MOC.Reformulations.NativeFirstB.spectralPageHull | Actual bigraded page complex and chain component; does not construct page transitions.
093 | Superalgebra | checked-native | MOC.Reformulations.NativeFirstB.berezinian_mem_quotient_hulls | Actual determinant quotient under the two block hulls, retaining the invertible odd denominator.
094 | Perfect complexes | finite-restriction | MOC.Reformulations.NativeFirstB.gradedOperatorDeterminantLine_of_moc | Signed finite degree products; no perfect-complex derived endomorphism construction.
095 | Reidemeister torsion | checked-native | MOC.Reformulations.NativeFirstB.reidemeisterFactor_mem_product | Exact norm multiplicative factor assertion; does not claim the matrices are adapted to a geometric acyclic complex.
096 | Ray-Singer analytic torsion | checked-native | MOC.Reformulations.NativeFirstB.finiteSpectralTorsion_bounds | Signed finite log-determinant bounds with permutation witnesses; no zeta limit.
097 | L2-torsion | finite-restriction | MOC.Reformulations.NativeFirstB.finiteSpectralTorsion_bounds | Finite normalized positive spectral blocks only; general operator determinant coupling and L2 invariance not formalized.
098 | Lefschetz fixed-point theory | checked-native | MOC.Reformulations.NativeFirstB.singularHomologyHull; MOC.Reformulations.NativeFirstB.lefschetzTrace_unitary | Actual homology determinant implication and unconditional trace invariance, not an assertion of a map of spaces inducing the sum.
099 | Euclidean linear deformation | checked-native | MOC.Reformulations.NativeFirstB.stretchHull | Actual positive Gram square roots of two finite linear deformations.
100 | Affine geometry | checked-native-iff | MOC.Reformulations.NativeFirstB.affineDerivativeForm_iff | Actual affine maps and their linear parts; translations do not enter.
101 | Projective geometry | checked-native-iff | MOC.Reformulations.NativeLinksB.projectiveLiftForm_iff (auditor) | Exact invertible normal lifts with fixed scales; singular sum allowed.
102 | Differential topology | checked-native | MOC.Reformulations.NativeFirstB.realFixedPointIndexHull | Actual Fréchet derivatives, real orthogonal mixing, fixed-point sign determinant under MOC.
103 | Riemannian geometry | checked-native | MOC.Reformulations.NativeFirstB.positiveMetricHull | Positive relative metric matrices in a reference-orthonormal frame.
104 | Pseudo-Riemannian geometry | checked-native | MOC.Reformulations.NativeFirstB.indefiniteRelativeFormHull | Actual G0 inverse relative matrices and bilinear-form preservation; no normality inferred from an indefinite metric.
105 | Hypersurface geometry | finite-restriction | MOC.Reformulations.NativeFirstB.realSymmetricGeometricHull | Actual symmetric shape operator matrices in orthonormal coordinates; no hypersurface construction.
106 | Ricci geometry | finite-restriction | MOC.Reformulations.NativeFirstB.realSymmetricGeometricHull | Actual relative Ricci operator matrices in a reference-orthonormal frame; no manifold tensor construction.
107 | Curvature operator | finite-restriction | MOC.Reformulations.NativeFirstB.realSymmetricGeometricHull | Actual symmetric curvature operator on chosen second-exterior coordinates; no Bianchi realization criterion.
108 | Kähler geometry | checked-native | MOC.Reformulations.NativeFirstB.kahlerMetricHull | Actual positive Hermitian relative metrics in a reference-unitary frame.
109 | Finsler geometry | finite-restriction | MOC.Reformulations.NativeFirstB.positiveMetricHull | Positive fundamental tensors at one specified direction once evaluated; no global Finsler metric construction.
110 | Hessian and Monge-Ampere geometry | checked-native | MOC.Reformulations.NativeFirstB.hessianHull | Actual iterated Fréchet derivative with symmetric Hessian hypotheses.
111 | Geometric measure theory | finite-restriction | MOC.Reformulations.NativeFirstB.stretchHull | Specified finite square Gram stretches; approximate differentials and arbitrary rectangular target not constructed.
112 | Symplectic linear maps | checked-native | MOC.Reformulations.NativeFirstB.symplecticNormalHull | Actual doubled skew form and orthogonal symplectic mixing.
113 | Williamson theory | checked-native | MOC.Reformulations.NativeFirstB.williamsonRepHull | Actual repeated positive Williamson spectra, not invariance under general symplectic congruence.
114 | Hamiltonian linearization | checked-native | MOC.Reformulations.NativeFirstB.hamiltonianLinearizationHull | Actual finite JH infinitesimal linearizations and skew-form-preserving frame.
115 | Hamiltonian torus actions | finite-restriction | MOC.Reformulations.NativeFirstB.momentVectorHull | One real-linear evaluation of actual finite moment-vector lists; does not construct a Hamiltonian torus action.
116 | Symplectic toric geometry | finite-restriction | MOC.Reformulations.NativeFirstB.momentVectorHull | One real-linear evaluation of supplied vertex vectors; does not construct a toric moment polytope.
117 | Geometric invariant theory | checked-native-iff | MOC.Reformulations.NativeLinksB.torusCharacterForm_iff | Actual integer powers evaluated at one common nonzero complex torus parameter.
118 | Contact geometry | finite-restriction | MOC.Reformulations.NativeFirstB.symplecticNormalHull | Actual finite symplectic normal transverse return matrix once supplied; no Reeb flow construction.
119 | Geometric quantization | finite-restriction | MOC.Reformulations.NativeFirstB.quantizedObservableHull | Actual algebra-represented operators as one model; no underlying geometric quantization functor.
120 | Poisson geometry | finite-restriction | MOC.Reformulations.NativeFirstB.hamiltonianLinearizationHull | Actual infinitesimal JH on a chosen symplectic leaf frame; no extraction of leaf dynamics from Poisson structure.
121 | Floer homology | native-open | No specified Floer theory or continuation map in source | Finite normal operator implication applies once a definite functor and induced Hermitian action are supplied; not a Floer construction.
122 | Maslov index theory | checked-native | MOC.Reformulations.NativeFirstB.unitaryPhaseOperatorHull | Actual phase spectra of the selected representative; no assertion about a winding or phase lift.
123 | Hamiltonian integrable systems | checked-native-iff | MOC.Reformulations.NativeLinksB.quantumIntegralsForm_iff; exists_realJointSpectrum_iff | Actual scalar linear evaluation of commuting Hermitian tuples; Lean proves existence of their real joint eigenlabels.
124 | Commutative algebra and schemes | finite-restriction | MOC.Reformulations.NativeFirstB.triangularMultiplicationNorm | Actual algebra norm equals a single vertex in a common triangular basis; local-factor structure/multiplicities not derived from a scheme.
125 | Algebraic varieties | checked-native | MOC.Reformulations.NativeFirstB.complexFixedPointDerivativeHull | Actual complex Fréchet derivatives in local fixed-point coordinates.
126 | Vector bundles | finite-restriction | MOC.Reformulations.NativeFirstB.pointwiseFiberHull | Actual normal matrices in selected fiber frames; not a construction of bundle endomorphisms or continuous frames.
127 | Line bundles | checked-native | MOC.Reformulations.NativeFirstB.lineFiberDet | Exact rank-one determinant equality.
128 | Higgs bundles | finite-restriction | MOC.Reformulations.NativeFirstB.higgsTrivializationHull | Actual divided endomorphisms and the determinant scalar, given a canonical-line frame; no holomorphic bundle construction.
129 | Harder-Narasimhan filtration | finite-restriction | MOC.Reformulations.NativeFirstB.slopeFiltrationLogHull | Actual exponential-slope operator and positive log bounds; no Harder–Narasimhan construction or degree identification.
130 | Toric algebraic geometry | native-iff at the section-weight level | projectiveToricSectionForm_iff | Two independently twisted projective section lists at a common torus point give all nonzero spectra. The geometric realization is in the proof map.
131 | Newton-Okounkov theory | paper native iff | See the flag valuation construction in the all-order proof map | Big line bundles on one variety and a common full-rank flag valuation realize both arbitrary complex lists in degree one.
132 | Intersection theory | finite-restriction | MOC.Reformulations.NativeFirstB.realSymmetricGeometricHull | Actual self-adjoint intersection forms in selected finite coordinates; no numerical cycles construction.
133 | Chern-Weil theory | finite-restriction | MOC.Reformulations.NativeFirstB.curvatureContractionHull | Actual skew-Hermitian curvature evaluations and Chern–Weil scalar; no top Chern-form or global connection construction.
-/
