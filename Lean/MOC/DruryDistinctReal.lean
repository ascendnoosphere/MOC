import MOC.DruryRealPhaseScalars
import MOC.DruryRealSpectrum
import MOC.RankOneOrbitDeterminant

/-! A pair of nonreal coefficients in the two real resolvent eigenspaces
produces a rank-one phase line through a Hermitian pencil support maximum. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1500000 in
/-- For two distinct real resolvent roots, an eigenvector of the two-parameter
pencil with both parameters nonreal rules out a quadratic support maximum. -/
theorem no_quadratic_support_of_distinct_real_pencil_vector (A E F : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hAi : IsUnit A.det) (hEA : (E * A).IsHermitian)
    (hFA : (F * A).IsHermitian) (hsum : E + F = 1)
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0) (hFE : F * E = 0)
    (r s : ℝ) (hrs : r ≠ s) (κ ξ a b : ℂ) (hκ : κ ≠ 0)
    (hr : 1 - κ * (r : ℂ) ≠ 0) (hs : 1 - κ * (s : ℂ) ≠ 0)
    (ha : a ≠ star a) (hb : b ≠ star b)
    (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (huA : A *ᵥ u = a • (E *ᵥ u) + b • (F *ᵥ u)) :
    let B := κ • (((r : ℂ) • E + (s : ℂ) • F) * A)
    let T := A - B
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - B).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  intro hT hpenalty
  let B := κ • (((r : ℂ) • E + (s : ℂ) • F) * A)
  let T := A - B
  let R := (1 - κ * (r : ℂ))⁻¹
  let S := (1 - κ * (s : ℂ))⁻¹
  let W := R • E + S • F
  let L : Matrix ι Unit ℂ := fun i _ => u i
  change IsUnit T.det at hT
  have hTfactor : T = ((1 - κ * (r : ℂ)) • E + (1 - κ * (s : ℂ)) • F) * A := by
    calc
      T = (E + F) * A - B := by simp only [T, hsum, Matrix.one_mul]
      _ = _ := by
        simp only [B, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, smul_add, smul_smul,
          sub_smul, one_smul]
        abel
  have hWfactor : W * ((1 - κ * (r : ℂ)) • E + (1 - κ * (s : ℂ)) • F) = 1 := by
    simp only [W, R, S, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, hEE, hFF, hEF, hFE, inv_mul_cancel₀ hr, inv_mul_cancel₀ hs,
      mul_inv_cancel₀ hr, mul_inv_cancel₀ hs, one_smul, smul_zero, add_zero, zero_add, hsum]
  have hWT : W * T = A := by rw [hTfactor, ← Matrix.mul_assoc, hWfactor, Matrix.one_mul]
  have hAT : A * T⁻¹ = W := by
    rw [← hWT, Matrix.mul_assoc, T.mul_nonsing_inv hT, Matrix.mul_one]
  have hTi : T⁻¹ = A⁻¹ * W := by
    rw [← hAT, ← Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.one_mul]
  have hnB : -B = T - A := by dsimp only [T]; abel
  have hTB : T⁻¹ * (-B) = 1 - A⁻¹ * W * A := by
    rw [hnB, Matrix.mul_sub, T.nonsing_inv_mul hT, hTi]
  have hWB : W * (-B) = A - W * A := by rw [hnB, Matrix.mul_sub, hWT]
  have hLA : A * L = a • (E * L) + b • (F * L) := by
    ext i j : 1
    simpa only [Matrix.mul_apply, L, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.add_apply] using congrFun huA i
  have hLE : (E * A) * L = a • (E * L) := by
    rw [Matrix.mul_assoc, hLA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc E E L, ← Matrix.mul_assoc E F L, hEE, hEF, Matrix.zero_mul,
      smul_zero, add_zero]
  have hLF : (F * A) * L = b • (F * L) := by
    rw [Matrix.mul_assoc, hLA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc F E L, ← Matrix.mul_assoc F F L, hFE, hFF, Matrix.zero_mul,
      smul_zero, zero_add]
  let f : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (Lᴴ * M * L) () ()
      map_add' := by
        intro M N
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := by
        intro t M
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply] }
  have hf (M : Matrix ι ι ℂ) : f M = (Lᴴ * M * L) () () := rfl
  have hfOne : f 1 = 1 := by
    rw [hf, Matrix.mul_one]
    simpa only [L, Matrix.mul_apply, Matrix.conjTranspose_apply] using hu
  have hfStar (M : Matrix ι ι ℂ) : f Mᴴ = star (f M) := by
    change (Lᴴ * Mᴴ * L) () () = (Lᴴ * M * L)ᴴ () ()
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hfCol (M N : Matrix ι ι ℂ) (t : ℂ) (he : M * L = t • (N * L)) :
      f M = t * f N := by
    simp only [hf, Matrix.mul_assoc, he, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  have hvalues (P : Matrix ι ι ℂ) (t : ℂ) (hPA : (P * A).IsHermitian)
      (hPL : (P * A) * L = t • (P * L)) :
      let k := (f (A⁻¹ * P)).re
      f (A⁻¹ * P) = (k : ℂ) ∧ f P = star t * (k : ℂ) ∧
        f (P * A) = t * (star t * (k : ℂ)) ∧ f (A⁻¹ * P * A) = t * (k : ℂ) := by
    let k := (f (A⁻¹ * P)).re
    have hdual : Pᴴ = A⁻¹ * P * A := by
      have he := hPA.eq
      rw [Matrix.conjTranspose_mul, hA.eq] at he
      calc
        Pᴴ = A⁻¹ * (A * Pᴴ) := by rw [← Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.one_mul]
        _ = _ := by rw [he, Matrix.mul_assoc]
    have hHP : (A⁻¹ * P).IsHermitian := by
      change (A⁻¹ * P)ᴴ = A⁻¹ * P
      rw [Matrix.conjTranspose_mul, hA.inv.eq, hdual, Matrix.mul_assoc (A⁻¹ * P),
        A.mul_nonsing_inv hAi, Matrix.mul_one]
    have hreal : (k : ℂ) = f (A⁻¹ * P) := by
      apply Complex.conj_eq_iff_re.mp
      rw [← Complex.star_def, ← hfStar, hHP.eq]
    have hleft : f (A⁻¹ * P * A) = t * (k : ℂ) := by
      rw [hreal]
      apply hfCol
      rw [Matrix.mul_assoc A⁻¹ P A, Matrix.mul_assoc A⁻¹ (P * A) L, hPL,
        Matrix.mul_smul, Matrix.mul_assoc]
    have hP : f P = star t * (k : ℂ) := by
      have he := (hfStar P).symm.trans ((congrArg f hdual).trans hleft)
      simpa only [star_star, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
        using congrArg star he
    exact ⟨hreal.symm, hP, (hfCol (P * A) P t hPL).trans (congrArg (t * ·) hP), hleft⟩
  let h := (f (A⁻¹ * E)).re
  let k := (f (A⁻¹ * F)).re
  obtain ⟨he₀, he₁, he₂, he₃⟩ := hvalues E a hEA hLE
  obtain ⟨hf₀, hf₁, hf₂, hf₃⟩ := hvalues F b hFA hLF
  change f (A⁻¹ * E) = (h : ℂ) at he₀
  change f (A⁻¹ * F) = (k : ℂ) at hf₀
  have hpair : a * (h : ℂ) + b * (k : ℂ) = 1 := by
    have hEf := congrArg f hsum
    rw [map_add, hfOne, he₁, hf₁] at hEf
    simpa only [star_add, star_mul', star_star, star_one, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_conj, mul_comm] using congrArg star hEf
  let t := κ * R * S
  let ℓ := ((r : ℂ) - (s : ℂ)) * (star a * (h : ℂ) - a * (h : ℂ))
  let K := (h : ℂ) * (k : ℂ) * ((s : ℂ) * (b * star b - star a * b) +
    (r : ℂ) * (a * star a - star b * a))
  have hα : (Lᴴ * A * T⁻¹ * L) () () = R * (star a * (h : ℂ)) + S * (star b * (k : ℂ)) := by
    rw [Matrix.mul_assoc Lᴴ A, hAT, ← hf]
    simp only [W, map_add, map_smul, smul_eq_mul, he₁, hf₁, h, k]
  have hβ : (Lᴴ * T⁻¹ * (-(B * L))) () () =
      (1 - R) * (a * (h : ℂ)) + (1 - S) * (b * (k : ℂ)) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_assoc (Lᴴ * T⁻¹), Matrix.mul_assoc Lᴴ T⁻¹,
      hTB, ← hf]
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_sub,
      map_add, map_smul, smul_eq_mul, hfOne, he₃, hf₃]
    linear_combination -hpair
  have hγ : (Lᴴ * A * T⁻¹ * (-(B * L))) () () =
      (1 - R) * (a * (star a * (h : ℂ))) + (1 - S) * (b * (star b * (k : ℂ))) := by
    rw [Matrix.mul_assoc Lᴴ A T⁻¹, hAT, ← Matrix.neg_mul,
      ← Matrix.mul_assoc (Lᴴ * W), Matrix.mul_assoc Lᴴ W, hWB, ← hf]
    have he : f A = f (E * A) + f (F * A) := by rw [← map_add, ← Matrix.add_mul, hsum, Matrix.one_mul]
    simp only [W, Matrix.add_mul, Matrix.smul_mul, map_sub, map_add, map_smul, smul_eq_mul, he,
      he₂, hf₂]
    ring
  have hε : (Lᴴ * T⁻¹ * L) () () = R * (h : ℂ) + S * (k : ℂ) := by
    rw [hTi, ← hf]
    simp only [W, Matrix.mul_add, Matrix.mul_smul, map_add, map_smul, smul_eq_mul, he₀, hf₀]
  obtain ⟨hlinear, hquad⟩ := drury_distinct_real_resolvent_phase_coefficients r s h k a b κ hr hs hpair
  obtain ⟨hℓ, hK⟩ := drury_distinct_real_phase_coefficients r s h k hrs a b ha hb hpair
  have hD : T.det * t ≠ 0 := mul_ne_zero (isUnit_iff_ne_zero.mp hT)
    (mul_ne_zero (mul_ne_zero hκ (inv_ne_zero hr)) (inv_ne_zero hs))
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

/-- Two distinct real resolvent roots force each auxiliary pencil eigenvalue
onto the real line or the line through its parameter. -/
theorem real_line_condition_of_distinct_real_pencil_support (A E F : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hAi : IsUnit A.det) (hEA : (E * A).IsHermitian)
    (hFA : (F * A).IsHermitian) (hsum : E + F = 1)
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0) (hFE : F * E = 0)
    (r s : ℝ) (hrs : r ≠ s) (κ ξ : ℂ) (hκ : κ ≠ 0)
    (hr : 1 - κ * (r : ℂ) ≠ 0) (hs : 1 - κ * (s : ℂ) ≠ 0) :
    let B := κ • (((r : ℂ) • E + (s : ℂ) • F) * A)
    let T := A - B
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - B).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) →
    ∀ z : ℂ, z ≠ 0 → ∀ x : ℂ,
      (x • (1 : Matrix ι ι ℂ) - (E * A + z • (F * A))).det = 0 →
      x = star x ∨ x / z = star (x / z) := by
  dsimp only
  intro hT hpenalty z hz x hx
  by_contra hn
  have hxn : x ≠ star x := fun he => hn (Or.inl he)
  have hzn : x / z ≠ star (x / z) := fun he => hn (Or.inr he)
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
  obtain ⟨d, hd⟩ := exists_normalized_complex_column v hv
  let u := d • v
  have hzero : (x • (1 : Matrix ι ι ℂ) - (E * A + z • (F * A))) *ᵥ u = 0 := by
    simp only [u, Matrix.mulVec_smul, hvz, smul_zero]
  have hu : ((E + z • F) * A) *ᵥ u = x • u := by
    rw [Matrix.add_mul, Matrix.smul_mul]
    exact (sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec] using hzero)).symm
  have hInv : (E + z⁻¹ • F) * (E + z • F) = 1 := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      hEE, hEF, hFE, hFF, smul_zero, inv_mul_cancel₀ hz, mul_inv_cancel₀ hz, one_smul,
      add_zero, zero_add, hsum]
  have he := congrArg (fun w : ι → ℂ => (E + z⁻¹ • F) *ᵥ w) hu
  change (E + z⁻¹ • F) *ᵥ (((E + z • F) * A) *ᵥ u) =
    (E + z⁻¹ • F) *ᵥ (x • u) at he
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hInv, Matrix.one_mul,
    Matrix.mulVec_smul (E + z⁻¹ • F) x u,
    Matrix.add_mulVec, Matrix.smul_mulVec_assoc, smul_add,
    smul_smul x z⁻¹ (F *ᵥ u)] at he
  exact no_quadratic_support_of_distinct_real_pencil_vector A E F hA hAi hEA hFA hsum
    hEE hFF hEF hFE r s hrs κ ξ x (x / z) hκ hr hs hxn hzn u hd
    (by simpa only [div_eq_mul_inv] using he) hT hpenalty

/-- A nonsingular support maximum for a Hermitian pencil cannot have two
distinct real resolvent roots and pairwise distinct spectral ratios. -/
theorem no_generic_quadratic_support_of_distinct_real_pencil {n : ℕ} (hn : 3 ≤ n)
    (A E F : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hAi : IsUnit A.det)
    (hEA : (E * A).IsHermitian) (hFA : (F * A).IsHermitian) (hsum : E + F = 1)
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0) (hFE : F * E = 0)
    (r s : ℝ) (hrs : r ≠ s) (hr₀ : r ≠ 0) (hs₀ : s ≠ 0)
    (κ ξ : ℂ) (hκ : κ ≠ 0) (hr : 1 - κ * (r : ℂ) ≠ 0) (hs : 1 - κ * (s : ℂ) ≠ 0)
    (a c : Fin n → ℂ) (ha : ∀ j, a j ≠ 0)
    (hbase : ∀ x, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = 0 → ∃ j, x = a j)
    (hother : ∀ i, (c i • (1 : Matrix (Fin n) (Fin n) ℂ) -
      ((r : ℂ) • E + (s : ℂ) • F) * A).det = 0)
    (hinj : Function.Injective (fun p : Fin n × Fin n => c p.1 / a p.2)) :
    let B := κ • (((r : ℂ) • E + (s : ℂ) • F) * A)
    let T := A - B
    IsUnit T.det →
    (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      let d := (V * A * Vᴴ - B).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  intro hT hpenalty
  have hsplit := real_line_condition_of_distinct_real_pencil_support A E F hA hAi hEA hFA hsum
    hEE hFF hEF hFE r s hrs κ ξ hκ hr hs hT hpenalty
  have hA' : E * A + F * A = A := by rw [← Matrix.add_mul, hsum, Matrix.one_mul]
  have hC' : (r : ℂ) • (E * A) + (s : ℂ) • (F * A) =
      ((r : ℂ) • E + (s : ℂ) • F) * A := by
    simp only [Matrix.add_mul, Matrix.smul_mul]
  exact (hermitian_pencil_ratios_not_injective hn (E * A) (F * A) hEA hFA hsplit a c ha
    (Complex.ofReal_ne_zero.mpr hr₀) (Complex.ofReal_ne_zero.mpr hs₀)
    (by simpa only [hA'] using hbase) (by simpa only [hC'] using hother)) hinj

/-- The distinct-real-root case of the Drury resolvent quadratic is impossible
at a generic Hermitian pencil quadratic support maximum. -/
theorem no_generic_quadratic_support_of_split_real_drury {n : ℕ} (hn : 3 ≤ n)
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAi : IsUnit A.det) (r s : ℝ) (hrs : r ≠ s) (hr₀ : r ≠ 0) (hs₀ : s ≠ 0)
    (κ ξ : ℂ) (hκ : κ ≠ 0) (hr : 1 - κ * (r : ℂ) ≠ 0) (hs : 1 - κ * (s : ℂ) ≠ 0)
    (a c : Fin n → ℂ) (ha : ∀ j, a j ≠ 0)
    (hbase : ∀ x, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = 0 → ∃ j, x = a j)
    (hother : ∀ i, (c i • (1 : Matrix (Fin n) (Fin n) ℂ) - C).det = 0)
    (hinj : Function.Injective (fun p : Fin n × Fin n => c p.1 / a p.2)) :
    let X := C * A⁻¹
    let T := A - κ • C
    (X - (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
      (X - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 →
    IsUnit T.det →
    (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      let d := (A - κ • (V * C * Vᴴ)).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  intro hsplit hT hpenalty
  let X := C * A⁻¹
  let P := X - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := (r : ℂ) - (s : ℂ)
  let E := d⁻¹ • P
  let F := 1 - E
  have hd : d ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hrs)
  have hfactor : X - (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = P - d • 1 := by
    dsimp only [P, d]
    rw [sub_smul]
    abel
  have hProd : P * P = d • P := by
    change (X - (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * P = 0 at hsplit
    rw [hfactor, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hsplit
    exact sub_eq_zero.mp hsplit
  have hEE : E * E = E := by
    simp only [E, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hProd, mul_assoc,
      inv_mul_cancel₀ hd, mul_one]
  have hEF : E * F = 0 := by simp only [F, Matrix.mul_sub, Matrix.mul_one, hEE, sub_self]
  have hFE : F * E = 0 := by simp only [F, Matrix.sub_mul, Matrix.one_mul, hEE, sub_self]
  have hFF : F * F = F := by rw [show F * F = F * (1 - E) from rfl, Matrix.mul_sub,
    Matrix.mul_one, hFE, sub_zero]
  have hsum : E + F = 1 := by dsimp only [F]; abel
  have hXA : X * A = C := by simp only [X, Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.mul_one]
  have hC' : ((r : ℂ) • E + (s : ℂ) • F) * A = C := by
    have he : (r : ℂ) • E + (s : ℂ) • F = X := calc
      _ = d • E + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        dsimp only [d, F]
        rw [smul_sub, sub_smul]
        abel
      _ = P + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        dsimp only [E]
        rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
      _ = X := by dsimp only [P]; abel
    rw [he, hXA]
  have hEA : (E * A).IsHermitian := by
    have he : E * A = d⁻¹ • (C - (s : ℂ) • A) := by
      dsimp only [E, P]
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hXA]
    have hstarD : star d = d := by simp [d, Complex.star_def]
    have hstarS : star (s : ℂ) = (s : ℂ) := by simp [Complex.star_def]
    rw [he]
    change (d⁻¹ • (C - (s : ℂ) • A))ᴴ = d⁻¹ • (C - (s : ℂ) • A)
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hA.eq, hC.eq, star_inv₀,
      hstarD, hstarS]
  have hFA : (F * A).IsHermitian := by
    rw [show F = 1 - E from rfl, Matrix.sub_mul, Matrix.one_mul]
    exact hA.sub hEA
  apply no_generic_quadratic_support_of_distinct_real_pencil hn A E F hA hAi hEA hFA hsum
    hEE hFF hEF hFE r s hrs hr₀ hs₀ κ ξ hκ hr hs a c ha hbase
    (by simpa only [hC'] using hother) hinj (by simpa only [hC'] using hT)
  intro V hV
  have hV' : IsUnitary Vᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
  have he : (V * A * Vᴴ - κ • C).det = (A - κ • (Vᴴ * C * V)).det := by
    rw [det_sub_unitary_conjugation_left A (κ • C) V hV, Matrix.mul_smul, Matrix.smul_mul]
  have hp := hpenalty Vᴴ hV'
  simp only [Matrix.conjTranspose_conjTranspose, ← he] at hp
  simpa only [hC'] using hp

end

end MOC
