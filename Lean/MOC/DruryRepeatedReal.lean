import MOC.DruryRealPhaseScalars
import MOC.DruryRealSpectrum
import MOC.RankOneOrbitDeterminant

/-! A nilpotent correction at a repeated real resolvent root gives a
rank-one phase line if the auxiliary pencil has a nonreal eigenvalue. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1500000 in
/-- The phase-line obstruction for a repeated real root. -/
theorem no_quadratic_support_of_repeated_real_pencil_vector (A N : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hAi : IsUnit A.det) (hNA : (N * A).IsHermitian) (hNN : N * N = 0)
    (ρ : ℝ) (κ ξ a b : ℂ) (hκ : κ ≠ 0) (hρ : 1 - κ * (ρ : ℂ) ≠ 0)
    (ha : a ≠ star a) (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (huA : A *ᵥ u = a • u + b • (N *ᵥ u)) :
    let B := κ • (((ρ : ℂ) • (1 : Matrix ι ι ℂ) + N) * A)
    let T := A - B
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - B).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  intro hT hpenalty
  let B := κ • (((ρ : ℂ) • (1 : Matrix ι ι ℂ) + N) * A)
  let T := A - B
  let d : ℂ := 1 - κ * (ρ : ℂ)
  let R := d⁻¹
  let t := κ * R ^ 2
  let W := R • (1 : Matrix ι ι ℂ) + t • N
  let L : Matrix ι Unit ℂ := fun i _ => u i
  change IsUnit T.det at hT
  have hTfactor : T = (d • (1 : Matrix ι ι ℂ) - κ • N) * A := by
    simp only [T, B, d, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      smul_add, smul_smul, sub_smul, one_smul]
    abel
  have hRd : R * d = 1 := inv_mul_cancel₀ hρ
  have htd : t * d = R * κ := by
    calc
      _ = R * κ * (R * d) := by dsimp only [t]; ring
      _ = _ := by rw [hRd, mul_one]
  have hWfactor : W * (d • (1 : Matrix ι ι ℂ) - κ • N) = 1 := by
    simp only [W, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, mul_comm d R, mul_comm d t,
      mul_comm κ R, hNN, hRd, one_smul, smul_zero, htd, add_zero]
    abel
  have hWT : W * T = A := by rw [hTfactor, ← Matrix.mul_assoc, hWfactor, Matrix.one_mul]
  have hAT : A * T⁻¹ = W := by rw [← hWT, Matrix.mul_assoc, T.mul_nonsing_inv hT, Matrix.mul_one]
  have hTi : T⁻¹ = A⁻¹ * W := by
    rw [← hAT, ← Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.one_mul]
  have hnB : -B = T - A := by dsimp only [T]; abel
  have hTB : T⁻¹ * (-B) = 1 - A⁻¹ * W * A := by
    rw [hnB, Matrix.mul_sub, T.nonsing_inv_mul hT, hTi]
  have hWB : W * (-B) = A - W * A := by rw [hnB, Matrix.mul_sub, hWT]
  have hLA : A * L = a • L + b • (N * L) := by
    ext i j : 1
    simpa only [Matrix.mul_apply, L, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.add_apply] using congrFun huA i
  have hLN : (N * A) * L = a • (N * L) := by
    rw [Matrix.mul_assoc, hLA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc N N L, hNN, Matrix.zero_mul, smul_zero, add_zero]
  let f : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (Lᴴ * M * L) () ()
      map_add' := by intro M Q; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := by
        intro x M
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply] }
  have hf (M : Matrix ι ι ℂ) : f M = (Lᴴ * M * L) () () := rfl
  have hfOne : f 1 = 1 := by
    rw [hf, Matrix.mul_one]
    simpa only [L, Matrix.mul_apply, Matrix.conjTranspose_apply] using hu
  have hfStar (M : Matrix ι ι ℂ) : f Mᴴ = star (f M) := by
    change (Lᴴ * Mᴴ * L) () () = (Lᴴ * M * L)ᴴ () ()
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hfCol (M Q : Matrix ι ι ℂ) (x : ℂ) (he : M * L = x • (Q * L)) :
      f M = x * f Q := by
    simp only [hf, Matrix.mul_assoc, he, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  have hdual : Nᴴ = A⁻¹ * N * A := by
    have he := hNA.eq
    rw [Matrix.conjTranspose_mul, hA.eq] at he
    calc
      Nᴴ = A⁻¹ * (A * Nᴴ) := by rw [← Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.one_mul]
      _ = _ := by rw [he, Matrix.mul_assoc]
  have hAN : (A⁻¹ * N).IsHermitian := by
    change (A⁻¹ * N)ᴴ = A⁻¹ * N
    rw [Matrix.conjTranspose_mul, hA.inv.eq, hdual, Matrix.mul_assoc (A⁻¹ * N),
      A.mul_nonsing_inv hAi, Matrix.mul_one]
  let c := (f A⁻¹).re
  let h := (f (A⁻¹ * N)).re
  have hreal (M : Matrix ι ι ℂ) (hM : M.IsHermitian) : (((f M).re : ℝ) : ℂ) = f M := by
    apply Complex.conj_eq_iff_re.mp
    rw [← Complex.star_def, ← hfStar, hM.eq]
  have hc : f A⁻¹ = (c : ℂ) := (hreal A⁻¹ hA.inv).symm
  have hh : f (A⁻¹ * N) = (h : ℂ) := (hreal (A⁻¹ * N) hAN).symm
  have hfDual : f (A⁻¹ * N * A) = a * (h : ℂ) := by
    rw [← hh]
    apply hfCol
    rw [Matrix.mul_assoc A⁻¹ N A, Matrix.mul_assoc A⁻¹ (N * A) L, hLN,
      Matrix.mul_smul, Matrix.mul_assoc]
  have hfN : f N = star a * (h : ℂ) := by
    have he := (hfStar N).symm.trans ((congrArg f hdual).trans hfDual)
    simpa only [star_star, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
      using congrArg star he
  let p := star a * (h : ℂ)
  have hfNA : f (N * A) = a * p := (hfCol (N * A) N a hLN).trans (congrArg (a * ·) hfN)
  have hfA : f A = a + b * p := by
    simp only [hf A, Matrix.mul_assoc Lᴴ A L, hLA, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, ← Matrix.mul_assoc Lᴴ N L, ← hf N, hfN]
    have he : (Lᴴ * L) () () = 1 := by
      simpa only [L, Matrix.mul_apply, Matrix.conjTranspose_apply] using hu
    rw [he, mul_one]
  have hpair : a * (c : ℂ) + b * (h : ℂ) = 1 := by
    have hcol : L = a • (A⁻¹ * L) + b • ((A⁻¹ * N) * L) := calc
      L = A⁻¹ * (A * L) := by rw [← Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.one_mul]
      _ = _ := by rw [hLA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc]
    have he := congrArg (fun Q : Matrix ι Unit ℂ => (Lᴴ * Q) () ()) hcol
    change (Lᴴ * L) () () = (Lᴴ * (a • (A⁻¹ * L) + b • ((A⁻¹ * N) * L))) () () at he
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      ← Matrix.mul_assoc Lᴴ A⁻¹ L, ← Matrix.mul_assoc Lᴴ (A⁻¹ * N) L,
      ← hf A⁻¹, ← hf (A⁻¹ * N), hc, hh] at he
    exact he.symm.trans (by simpa only [L, Matrix.mul_apply, Matrix.conjTranspose_apply] using hu)
  let ℓ := p - star p
  let K := (p * (c : ℂ) - (h : ℂ)) * ((ρ : ℂ) * b + a)
  have hα : (Lᴴ * A * T⁻¹ * L) () () = R + t * p := by
    rw [Matrix.mul_assoc Lᴴ A, hAT, ← hf]
    simp only [W, map_add, map_smul, hfOne, hfN, smul_eq_mul, mul_one, p]
  have hβ : (Lᴴ * T⁻¹ * (-(B * L))) () () = 1 - R - t * (a * (h : ℂ)) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_assoc (Lᴴ * T⁻¹), Matrix.mul_assoc Lᴴ T⁻¹, hTB, ← hf]
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      A.nonsing_inv_mul hAi, map_sub, map_add, map_smul, smul_eq_mul, hfOne, hfDual, mul_one]
    ring
  have hγ : (Lᴴ * A * T⁻¹ * (-(B * L))) () () = (1 - R) * (a + b * p) - t * (a * p) := by
    rw [Matrix.mul_assoc Lᴴ A T⁻¹, hAT, ← Matrix.neg_mul,
      ← Matrix.mul_assoc (Lᴴ * W), Matrix.mul_assoc Lᴴ W, hWB, ← hf]
    simp only [W, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, map_sub, map_add, map_smul,
      smul_eq_mul, hfA, hfNA]
    ring
  have hε : (Lᴴ * T⁻¹ * L) () () = R * (c : ℂ) + t * (h : ℂ) := by
    rw [hTi, ← hf]
    simp only [W, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, map_add, map_smul, smul_eq_mul,
      hc, hh]
  obtain ⟨hlinear, hquad⟩ := drury_repeated_real_resolvent_phase_coefficients ρ c h a b κ hρ hpair
  obtain ⟨hℓ, hK⟩ := drury_repeated_real_phase_coefficients ρ c h a b ha hpair
  have hD : T.det * t ≠ 0 := mul_ne_zero (isUnit_iff_ne_zero.mp hT)
    (mul_ne_zero hκ (pow_ne_zero _ (inv_ne_zero hρ)))
  apply no_quadratic_support_of_laurent_phase_line ξ (T.det * t) ℓ K hD hℓ hK
  intro z hz
  let V := rankOnePhase u z
  have he := det_rankOnePhase_left_conjugation A B u hu z hz hT
  change (V * A * Vᴴ - B).det = T.det *
    (1 + (1 - star z) * ((Lᴴ * A * T⁻¹ * L) () () + (Lᴴ * T⁻¹ * (-(B * L))) () () - 1) +
    (z + star z - 2) * ((Lᴴ * A * T⁻¹ * L) () () * (Lᴴ * T⁻¹ * (-(B * L))) () () -
      (Lᴴ * A * T⁻¹ * (-(B * L))) () () * (Lᴴ * T⁻¹ * L) () ())) at he
  rw [hα, hβ, hγ, hε, hlinear, hquad] at he
  have hd : (V * A * Vᴴ - B).det - T.det =
      ((1 - star z) * ℓ + (z + star z - 2) * K) * (T.det * t) := by
    rw [he]
    ring
  have hp := hpenalty V (rankOnePhase_unitary u z hu hz)
  change (ξ * ((V * A * Vᴴ - B).det - T.det)).re ≤
    -Complex.normSq ((V * A * Vᴴ - B).det - T.det) / 2 at hp
  rwa [hd] at hp

/-- The repeated-root phase obstruction forces a nilpotent affine pencil to
have real spectrum for every complex parameter. -/
theorem real_roots_of_repeated_real_pencil_support (A N : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hAi : IsUnit A.det) (hNA : (N * A).IsHermitian) (hNN : N * N = 0)
    (ρ : ℝ) (κ ξ : ℂ) (hκ : κ ≠ 0) (hρ : 1 - κ * (ρ : ℂ) ≠ 0) :
    let B := κ • (((ρ : ℂ) • (1 : Matrix ι ι ℂ) + N) * A)
    let T := A - B
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - B).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) →
    ∀ z x : ℂ, (x • (1 : Matrix ι ι ℂ) - (A + z • (N * A))).det = 0 → star x = x := by
  dsimp only
  intro hT hpenalty z x hx
  by_contra hn
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
  obtain ⟨d, hd⟩ := exists_normalized_complex_column v hv
  let u := d • v
  have hzero : (x • (1 : Matrix ι ι ℂ) - (A + z • (N * A))) *ᵥ u = 0 := by
    simp only [u, Matrix.mulVec_smul, hvz, smul_zero]
  have hu : ((1 + z • N) * A) *ᵥ u = x • u := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    exact (sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec] using hzero)).symm
  have hInv : ((1 : Matrix ι ι ℂ) - z • N) * (1 + z • N) = 1 := by
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, smul_smul, hNN, smul_zero, sub_zero]
    abel
  have he := congrArg (fun w : ι → ℂ => ((1 : Matrix ι ι ℂ) - z • N) *ᵥ w) hu
  change (1 - z • N) *ᵥ (((1 + z • N) * A) *ᵥ u) = (1 - z • N) *ᵥ (x • u) at he
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hInv, Matrix.one_mul,
    Matrix.mulVec_smul ((1 : Matrix ι ι ℂ) - z • N) x u,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, smul_sub,
    smul_smul x z (N *ᵥ u)] at he
  exact no_quadratic_support_of_repeated_real_pencil_vector A N hA hAi hNA hNN ρ κ ξ x (-(x * z))
    hκ hρ (Ne.symm hn) u hd (by simpa only [sub_eq_add_neg, neg_smul] using he) hT hpenalty

/-- The repeated-real-root case forces all eigenvalues of the second Hermitian
summand to be a single rescaling of eigenvalues of the first. Generic spectral
ratios preclude this at a quadratic support maximum. -/
theorem no_generic_quadratic_support_of_repeated_real_drury {n : ℕ} (hn : 2 ≤ n)
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAi : IsUnit A.det) (ρ : ℝ) (hρ₀ : ρ ≠ 0)
    (κ ξ : ℂ) (hκ : κ ≠ 0) (hρ : 1 - κ * (ρ : ℂ) ≠ 0)
    (a c : Fin n → ℂ) (ha : ∀ j, a j ≠ 0)
    (hbase : ∀ x, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = 0 → ∃ j, x = a j)
    (hother : ∀ i, (c i • (1 : Matrix (Fin n) (Fin n) ℂ) - C).det = 0)
    (hinj : Function.Injective (fun p : Fin n × Fin n => c p.1 / a p.2)) :
    let N := C * A⁻¹ - (ρ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
    let T := A - κ • C
    N * N = 0 → IsUnit T.det →
    (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      let d := (A - κ • (V * C * Vᴴ)).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  intro hNN hT hpenalty
  let N := C * A⁻¹ - (ρ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  change N * N = 0 at hNN
  have hNA : N * A = C - (ρ : ℂ) • A := by
    simp only [N, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
      A.nonsing_inv_mul hAi, Matrix.mul_one]
  have hNA' : (N * A).IsHermitian := by
    rw [hNA]
    change (C - (ρ : ℂ) • A)ᴴ = C - (ρ : ℂ) • A
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hC.eq, hA.eq,
      Complex.star_def, Complex.conj_ofReal]
  have hC' : ((ρ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + N) * A = C := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hNA]
    abel
  have hleft : ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - κ • C).det - (A - κ • C).det
      (ξ * d).re ≤ -Complex.normSq d / 2 := by
    intro V hV
    have hV' : IsUnitary Vᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
    have he : (V * A * Vᴴ - κ • C).det = (A - κ • (Vᴴ * C * V)).det := by
      rw [det_sub_unitary_conjugation_left A (κ • C) V hV, Matrix.mul_smul, Matrix.smul_mul]
    have hp := hpenalty Vᴴ hV'
    simpa only [Matrix.conjTranspose_conjTranspose, ← he] using hp
  have hspectrum := real_roots_of_repeated_real_pencil_support A N hA hAi hNA' hNN ρ κ ξ hκ hρ
    (by simpa only [hC'] using hT) (by simpa only [hC'] using hleft)
  have hρn : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ₀
  let D := A + (ρ : ℂ)⁻¹ • (N * A)
  have hD : D.charpoly = A.charpoly :=
    charpoly_affine_constant_of_real_roots A (N * A) hspectrum (ρ : ℂ)⁻¹
  have hCD : C = (ρ : ℂ) • D := by
    rw [← hC']
    simp only [D, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul,
      mul_inv_cancel₀ hρn, one_smul]
  have hcover (i : Fin n) : ∃ j, c i / a j = (ρ : ℂ) := by
    have ht : c i • (1 : Matrix (Fin n) (Fin n) ℂ) - C =
        (ρ : ℂ) • ((c i / (ρ : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) - D) := by
      have hcancel : (ρ : ℂ) * (c i / (ρ : ℂ)) = c i := by rw [mul_comm, div_mul_cancel₀ _ hρn]
      simp only [smul_sub, smul_smul, hcancel, hCD]
    have hz := hother i
    rw [ht, Matrix.det_smul] at hz
    have hzD := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hρn)
    rw [← eval_matrixCharpoly, hD, eval_matrixCharpoly] at hzD
    obtain ⟨j, hj⟩ := hbase (c i / (ρ : ℂ)) hzD
    have he : c i = (ρ : ℂ) * a j := by rw [mul_comm, ← hj, div_mul_cancel₀ _ hρn]
    exact ⟨j, by rw [he, mul_div_cancel_right₀ _ (ha j)]⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  obtain ⟨j₀, hj₀⟩ := hcover i₀
  obtain ⟨j₁, hj₁⟩ := hcover i₁
  have he : (i₀, j₀) = (i₁, j₁) := hinj (hj₀.trans hj₁.symm)
  have hval : (0 : ℕ) = 1 := congrArg (fun p : Fin n × Fin n => p.1.val) he
  omega

end

end MOC
