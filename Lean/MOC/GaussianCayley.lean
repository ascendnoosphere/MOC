import MOC.Core
import MOC.CircleSpectra
import MOC.Reformulations.NativeLinksBGaussian
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.NoncommRing

open scoped ComplexOrder
open Matrix
namespace MOC
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "𝕄" => Matrix ι ι ℂ

/-- The forward coordinate map on skew-Hermitian matrices. -/
def cayleyMixer (K : 𝕄) : 𝕄 := (1 + K) * (1 - K)⁻¹

theorem isUnit_cayley_denominator (K : 𝕄) (hK : Kᴴ = -K) :
    IsUnit (1 - K : 𝕄) := by
  have hP : (1 + Kᴴ * K : 𝕄).PosDef :=
    (Matrix.PosDef.one : (1 : 𝕄).PosDef).add_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self K)
  have he : (1 + Kᴴ * K : 𝕄) = (1 + K) * (1 - K) := by
    rw [hK]
    noncomm_ring
  rw [he] at hP
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (by
    have h := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
    rw [Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_right h)

theorem isUnitary_cayleyMixer (K : 𝕄) (hK : Kᴴ = -K) :
    IsUnitary (cayleyMixer K) := by
  let P : 𝕄 := 1 + K
  let Q : 𝕄 := 1 - K
  have hPQ : Pᴴ = Q := by simp [P, Q, hK, sub_eq_add_neg]
  have hQP : Qᴴ = P := by simp [P, Q, hK]
  have hcomm : Q * P = P * Q := by dsimp [P, Q]; noncomm_ring
  have hQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp (isUnit_cayley_denominator K hK)
  have hc : (P * Q⁻¹)ᴴ * (P * Q⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_nonsing_inv,
      Matrix.mul_assoc, ← Matrix.mul_assoc Q P Q⁻¹, hcomm, Matrix.mul_assoc P Q Q⁻¹,
      Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one, hQP,
      Matrix.nonsing_inv_mul P (by
        rw [← hQP]
        simpa only [Matrix.det_conjTranspose] using hQ.star)]
  exact ⟨Matrix.mul_eq_one_comm.mp hc, hc⟩


/-- Every unitary with invertible `1 + U` has an explicit skew-Hermitian
coordinate. No spectral diagonalization or search is needed. -/
theorem exists_cayleyMixer_eq_of_isUnit_add_one (U : 𝕄) (hU : IsUnitary U)
    (hInv : IsUnit (1 + U : 𝕄)) :
    ∃ K : 𝕄, Kᴴ = -K ∧ cayleyMixer K = U := by
  let Q : 𝕄 := 1 + U
  let P : 𝕄 := U - 1
  let K := P * Q⁻¹
  have hQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hInv
  have hQa : IsUnit Qᴴ.det := by
    simpa only [Matrix.det_conjTranspose] using hQ.star
  have hKQ : K * Q = P := by
    simp [K, Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ]
  have hQaP : Qᴴ * P = -(Pᴴ * Q) := by
    simp only [Q, P, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_sub]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_add, hU.2]
    abel
  have hJ : Kᴴ = -K := by
    have h := congrArg (fun T : 𝕄 => Tᴴ) hKQ
    change (K * Q)ᴴ = Pᴴ at h
    rw [Matrix.conjTranspose_mul] at h
    have hleft : Qᴴ * (Kᴴ * Q) = Pᴴ * Q := by rw [← Matrix.mul_assoc, h]
    have hright : Qᴴ * (-K * Q) = Pᴴ * Q := by
      rw [Matrix.neg_mul, hKQ, Matrix.mul_neg, hQaP, neg_neg]
    have hh := congrArg (fun T : 𝕄 => Qᴴ⁻¹ * T * Q⁻¹) (hleft.trans hright.symm)
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Qᴴ hQa, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hQ] using hh
  refine ⟨K, hJ, ?_⟩
  have hmul : (1 + K : 𝕄) * Q = (U * (1 - K)) * Q := by
    rw [Matrix.add_mul, Matrix.one_mul, hKQ, Matrix.mul_assoc U,
      Matrix.sub_mul, Matrix.one_mul, hKQ]
    dsimp [Q, P]
    noncomm_ring
  have he : (1 + K : 𝕄) = U * (1 - K) := by
    have h := congrArg (fun T : 𝕄 => T * Q⁻¹) hmul
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hQ] using h
  have hK' : IsUnit (1 - K : 𝕄).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_cayley_denominator K hJ)
  rw [cayleyMixer, he, Matrix.mul_nonsing_inv_cancel_right _ _ hK']


private def ratPair (p : ℚ × ℚ) : ℂ := ⟨p.1, p.2⟩

/-- The concrete subfield of complex numbers with rational Cartesian coordinates. -/
def gaussianRationalSubfield : Subfield ℂ where
  carrier := Set.range ratPair
  one_mem' := ⟨(1, 0), by apply Complex.ext <;> simp [ratPair]⟩
  zero_mem' := ⟨(0, 0), by apply Complex.ext <;> simp [ratPair]⟩
  add_mem' := by
    rintro _ _ ⟨⟨a,b⟩,rfl⟩ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a+c,b+d), by apply Complex.ext <;> simp [ratPair]⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a,b⟩,rfl⟩ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a*c-b*d,a*d+b*c), by
      apply Complex.ext <;> simp [ratPair, Complex.mul_re, Complex.mul_im]⟩
  neg_mem' := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(-a,-b), by apply Complex.ext <;> simp [ratPair]⟩
  inv_mem' := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(a/(a*a+b*b),-b/(a*a+b*b)), by
      apply Complex.ext <;>
        simp [ratPair, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]⟩

theorem star_mem_gaussianRationalSubfield {z : ℂ}
    (h : z ∈ gaussianRationalSubfield) : star z ∈ gaussianRationalSubfield := by
  rcases h with ⟨⟨a,b⟩,rfl⟩
  exact ⟨(a,-b), by apply Complex.ext <;> simp [ratPair, Complex.star_def]⟩

theorem dense_gaussianRationalSubfield : Dense (gaussianRationalSubfield : Set ℂ) := by
  change DenseRange ratPair
  let f : ℚ × ℚ → ℝ × ℝ := Prod.map (fun t : ℚ => (t : ℝ)) (fun t : ℚ => (t : ℝ))
  have hd : DenseRange f := Rat.denseRange_cast.prodMap Rat.denseRange_cast
  let e := Complex.equivRealProdCLM.toHomeomorph.symm
  exact e.surjective.denseRange.comp hd e.continuous

private theorem inv_mem_subfield_matrix (F : Subfield ℂ) (A : 𝕄)
    (hA : ∀ i j, A i j ∈ F) (i j : ι) : A⁻¹ i j ∈ F := by
  let B : Matrix ι ι F := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : F.subtype.mapMatrix B = A := rfl
  have hdet : A.det ∈ F := by
    rw [← hB, ← F.subtype.map_det]
    exact B.det.property
  have hadj : A.adjugate i j ∈ F := by
    rw [← hB, ← F.subtype.map_adjugate]
    exact (B.adjugate i j).property
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact F.mul_mem (F.inv_mem hdet) hadj

private theorem cayleyMixer_mem_subfield (F : Subfield ℂ) (K : 𝕄)
    (hK : ∀ i j, K i j ∈ F) (i j : ι) : cayleyMixer K i j ∈ F := by
  have hone (i j : ι) : (1 : 𝕄) i j ∈ F := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h, F.one_mem, F.zero_mem]
  rw [cayleyMixer, Matrix.mul_apply]
  refine F.sum_mem ?_
  intro l _
  exact F.mul_mem (F.add_mem (hone _ _) (hK _ _))
    (inv_mem_subfield_matrix F (1 - K) (fun p q => F.sub_mem (hone p q) (hK p q)) _ _)


open scoped Topology
private def skewProjection (K : 𝕄) : 𝕄 := (2 : ℂ)⁻¹ • (K - Kᴴ)

omit [Fintype ι] [DecidableEq ι] in
private theorem skewProjection_skew (K : 𝕄) : (skewProjection K)ᴴ = -skewProjection K := by
  rw [skewProjection, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
  have hs : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp [Complex.star_def]
  rw [hs]

omit [Fintype ι] [DecidableEq ι] in
private theorem skewProjection_eq_of_skew (K : 𝕄) (hK : Kᴴ = -K) :
    skewProjection K = K := by
  ext i j
  simp only [skewProjection, hK, sub_neg_eq_add, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

private theorem continuousAt_cayleyMixer (K : 𝕄) (hK : Kᴴ = -K) :
    ContinuousAt cayleyMixer K := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_cayley_denominator K hK)
  have hinv : ContinuousAt Inv.inv (1 - K : 𝕄) :=
    continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hd.ne_zero)
  exact (continuous_const.add continuous_id).continuousAt.mul
    (hinv.comp (continuous_const.sub continuous_id).continuousAt)

theorem exists_subfield_unitary_mem_open_of_skew
    (F : Subfield ℂ) (hF : Dense (F : Set ℂ))
    (hstar : ∀ z ∈ F, star z ∈ F)
    {O : Set 𝕄} (hO : IsOpen O) (K : 𝕄) (hK : Kᴴ = -K)
    (hKO : cayleyMixer K ∈ O) :
    ∃ V ∈ O, IsUnitary V ∧ ∀ i j, V i j ∈ F := by
  let f (X : 𝕄) : 𝕄 := cayleyMixer (skewProjection X)
  have hf : ContinuousAt f K := (continuousAt_cayleyMixer _ (skewProjection_skew K)).comp
    (show ContinuousAt skewProjection K from
      (continuous_const.smul (continuous_id.sub (by fun_prop))).continuousAt)
  have hm : f K ∈ O := by simpa only [f, skewProjection_eq_of_skew K hK] using hKO
  have hN : f ⁻¹' O ∈ 𝓝 K := hf.preimage_mem_nhds (hO.mem_nhds hm)
  have hD : Dense {X : 𝕄 | ∀ i j, X i j ∈ F} := by
    have he : (Set.univ.pi fun _ : ι =>
        Set.univ.pi fun _ : ι => (F : Set ℂ)) = {X : 𝕄 | ∀ i j, X i j ∈ F} := by
      ext X; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_setOf_eq]; rfl
    rw [← he]
    simpa only [Set.pi_univ, Set.mem_setOf_eq] using
      (dense_pi (Set.univ : Set ι) (fun _ _ =>
        dense_pi (Set.univ : Set ι) (fun _ _ => hF)))
  obtain ⟨X, hXO, hXF⟩ := mem_closure_iff_nhds.mp (hD K) _ hN
  refine ⟨f X, hXO, isUnitary_cayleyMixer _ (skewProjection_skew X), ?_⟩
  apply cayleyMixer_mem_subfield
  intro i j
  exact F.mul_mem (F.inv_mem (by simpa only [one_add_one_eq_two] using F.add_mem F.one_mem F.one_mem))
    (F.sub_mem (hXF i j) (hstar _ (hXF j i)))

/-- Dense star-stable subfields give dense exact unitary entries once the
Cayley chart is known to meet every unitary neighborhood. -/
theorem exists_subfield_unitary_mem_open_of_cayley_chart
    (F : Subfield ℂ) (hF : Dense (F : Set ℂ))
    (hstar : ∀ z ∈ F, star z ∈ F)
    (hchart : ∀ (O : Set 𝕄), IsOpen O → ∀ U ∈ O, IsUnitary U →
      ∃ K : 𝕄, Kᴴ = -K ∧ cayleyMixer K ∈ O)
    {O : Set 𝕄} (hO : IsOpen O) (U : 𝕄) (hu : U ∈ O) (hU : IsUnitary U) :
    ∃ V ∈ O, IsUnitary V ∧ ∀ i j, V i j ∈ F := by
  obtain ⟨K, hK, hkO⟩ := hchart O hO U hu hU
  exact exists_subfield_unitary_mem_open_of_skew F hF hstar hO K hK hkO


theorem conjecture_iff_gaussian_rational_mixer_of_cayley_chart
    (hchart : ∀ (O : Set 𝕄), IsOpen O → ∀ U ∈ O, IsUnitary U →
      ∃ K : 𝕄, Kᴴ = -K ∧ cayleyMixer K ∈ O) :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : 𝕄),
      IsUnitary U → (∀ i j, U i j ∈ gaussianRationalSubfield) → Holds a b U := by
  constructor
  · intro h a b U hU _
    exact h a b U hU
  · intro h a b U hU
    by_contra hbad
    have hc : IsClosed {V : 𝕄 | Holds a b V} :=
      (Set.finite_range (matchingProduct a b)).isClosed_convexHull.preimage
        (show Continuous (determinantValue a b) by unfold determinantValue; fun_prop)
    obtain ⟨V, hVbad, hV, hVrat⟩ :=
      exists_subfield_unitary_mem_open_of_cayley_chart gaussianRationalSubfield
        dense_gaussianRationalSubfield (fun _ => star_mem_gaussianRationalSubfield)
        hchart hc.isOpen_compl U hbad hU
    exact hVbad (h a b V hV hVrat)

/-- The Cayley chart meets every open neighborhood of every unitary. -/
theorem exists_cayleyMixer_mem_open {O : Set 𝕄} (hO : IsOpen O)
    (U : 𝕄) (hU : IsUnitary U) (hu : U ∈ O) :
    ∃ K : 𝕄, Kᴴ = -K ∧ cayleyMixer K ∈ O := by
  classical
  let V (t : ℝ) : 𝕄 := circleRotation t • U
  have hcont : Continuous V := continuous_circleRotation.smul continuous_const
  have hzero : V 0 = U := by simp [V, circleRotation]
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp (hO.preimage hcont) 0
    (show V 0 ∈ O from hzero ▸ hu)
  let P : Polynomial ℂ :=
    (1 + (Polynomial.X : Polynomial ℂ) • (Polynomial.C.mapMatrix U)).det
  have he (z : ℂ) : P.eval z = (1 + z • U).det := by
    let f := Polynomial.evalRingHom z
    have hm : f.mapMatrix (Polynomial.C.mapMatrix U) = U := by
      ext i j
      simp [f, RingHom.mapMatrix_apply]
    have hs : f.mapMatrix ((Polynomial.X : Polynomial ℂ) • Polynomial.C.mapMatrix U) = z • U := by
      rw [show f.mapMatrix ((Polynomial.X : Polynomial ℂ) • Polynomial.C.mapMatrix U) =
        f (Polynomial.X : Polynomial ℂ) • f.mapMatrix (Polynomial.C.mapMatrix U) by
          ext i j
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]]
      rw [hm]
      simp [f]
    change f P = _
    simp only [P, f.map_det, map_add, map_one, hs]
  have hP : P ≠ 0 := by
    intro h
    have hz := he 0
    simp [h] at hz
  have hf : (circleRotation ⁻¹' {z | P.IsRoot z}).Finite :=
    (Polynomial.finite_setOf_isRoot hP).preimage circleRotation_injective.injOn
  have hinf : (Set.Ioo (-ε) ε).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨t, ht, hn⟩ := hinf.exists_not_mem_finite hf
  have htO : V t ∈ O := hεO (Metric.mem_ball.mpr (by
    simpa only [Real.dist_eq, sub_zero] using abs_lt.mpr ht))
  have htne : P.eval (circleRotation t) ≠ 0 := by
    intro hh
    exact hn hh
  have hscalar : star (circleRotation t) * circleRotation t = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, circleRotation_normSq]
    simp
  have hV : IsUnitary (V t) := by
    have heq : (V t)ᴴ * V t = 1 := by
      simp only [V, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hU.2,
        smul_smul, hscalar, one_smul]
      rw [mul_comm, hscalar, one_smul]
    exact ⟨Matrix.mul_eq_one_comm.mp heq, heq⟩
  have hinv : IsUnit (1 + V t : 𝕄) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (he _ ▸ htne))
  obtain ⟨K, hK, hKV⟩ := exists_cayleyMixer_eq_of_isUnit_add_one (V t) hV hinv
  exact ⟨K, hK, hKV ▸ htO⟩


/-- Exact symbolic density of unitaries with Gaussian-rational entries. -/
theorem exists_gaussian_rational_unitary_mem_open
    {O : Set 𝕄} (hO : IsOpen O) (U : 𝕄) (hu : U ∈ O) (hU : IsUnitary U) :
    ∃ V ∈ O, IsUnitary V ∧ ∀ i j, V i j ∈ gaussianRationalSubfield :=
  exists_subfield_unitary_mem_open_of_cayley_chart gaussianRationalSubfield
    dense_gaussianRationalSubfield (fun _ => star_mem_gaussianRationalSubfield)
    (fun _ ho V hv hV => exists_cayleyMixer_mem_open ho V hV hv) hO U hu hU

/-- Simultaneously restrict the spectra to Gaussian integers and the
mixer to Gaussian-rational exact unitaries. The hull test is unchanged. -/
theorem mocIsTrue_iff_gaussian_spectra_rational_mixer :
    MOCIsTrue ↔ ∀ (n : ℕ) (a b : Fin n → ℤ × ℤ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → (∀ i j, U i j ∈ gaussianRationalSubfield) →
      Holds (fun i => (a i).1 + (a i).2 * Complex.I)
        (fun i => (b i).1 + (b i).2 * Complex.I) U := by
  constructor
  · intro h n a b U hU _
    exact h n _ _ U hU
  · intro h
    apply Reformulations.NativeLinksB.gaussianSpectrumForm_iff.mp
    intro n a b U hU
    let x : Fin n → ℂ := fun i => (a i).1 + (a i).2 * Complex.I
    let y : Fin n → ℂ := fun i => (b i).1 + (b i).2 * Complex.I
    change Holds x y U
    by_contra hbad
    have hc : IsClosed {V : Matrix (Fin n) (Fin n) ℂ | Holds x y V} :=
      (Set.finite_range (matchingProduct x y)).isClosed_convexHull.preimage
        (show Continuous (determinantValue x y) by unfold determinantValue; fun_prop)
    obtain ⟨V, hVbad, hV, hVrat⟩ :=
      exists_gaussian_rational_unitary_mem_open hc.isOpen_compl U hbad hU
    exact hVbad (h n a b V hV hVrat)

end
end MOC
