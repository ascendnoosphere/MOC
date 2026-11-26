import MOC.GaussianCayley
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! A division-free test of the Marcus–de Oliveira conjecture on Gaussian integers. -/

open BigOperators Matrix

namespace MOC

private def gaussianI : GaussianInt := ⟨0, 1⟩

private def gaussianMatching {n : ℕ} (a b : Fin n → GaussianInt)
    (σ : Equiv.Perm (Fin n)) : GaussianInt :=
  ∏ j, (a (σ j) + b j)

private def gaussianEntryMatrix {n : ℕ} (a b : Fin n → GaussianInt)
    (V : Matrix (Fin n) (Fin n) GaussianInt) : Matrix (Fin n) (Fin n) GaussianInt :=
  Matrix.of fun i j => (a i + b j) * V i j

private def gaussianIntegerSupport {n : ℕ} (a b : Fin n → GaussianInt)
    (V : Matrix (Fin n) (Fin n) GaussianInt) (k : GaussianInt) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    (k * (star V.det * (gaussianEntryMatrix a b V).det)).re ≤
      (k * ((star V.det * V.det) * gaussianMatching a b σ)).re

/-- Compare the integer projections in the four axis directions and in each
normal from an ordered pair of matching products. -/
def GaussianIntegerDeterminantTest {n : ℕ} (a b : Fin n → GaussianInt)
    (V : Matrix (Fin n) (Fin n) GaussianInt) : Prop :=
  gaussianIntegerSupport a b V 1 ∧ gaussianIntegerSupport a b V (-1) ∧
    gaussianIntegerSupport a b V gaussianI ∧ gaussianIntegerSupport a b V (-gaussianI) ∧
    ∀ r s : Equiv.Perm (Fin n),
      gaussianIntegerSupport a b V (gaussianI * star (gaussianMatching a b r - gaussianMatching a b s))

private theorem gaussianGram_map_iff {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt) (d : ℕ) :
    Vᴴ * V = (d : GaussianInt)^2 • 1 ↔
      (V.map GaussianInt.toComplex)ᴴ * V.map GaussianInt.toComplex = (d : ℂ)^2 • 1 := by
  let g := GaussianInt.toComplex
  have hm : Function.Injective (fun M : Matrix (Fin n) (Fin n) GaussianInt => M.map g) := by
    intro A B h
    apply Matrix.ext
    intro i j
    exact GaussianInt.toComplex_injective (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h)
  have hs := Matrix.conjTranspose_map (A := V) g GaussianInt.toComplex_star
  rw [← hm.eq_iff]
  simp only [Matrix.map_mul, hs, Matrix.map_smul' g _ _ (map_mul g), map_pow, map_natCast,
    Matrix.map_one g (map_zero g) (map_one g)]
  rfl

private theorem star_natCast_complex (d : ℕ) : star (d : ℂ) = (d : ℂ) := by
  apply Complex.ext <;> simp [Complex.star_def]

private theorem exists_unitary_of_gaussianGram {n : ℕ}
    (V : Matrix (Fin n) (Fin n) GaussianInt) (d : ℕ) (hd : d ≠ 0)
    (hV : Vᴴ * V = (d : GaussianInt)^2 • 1) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, IsUnitary U ∧ V.map GaussianInt.toComplex = (d : ℂ) • U := by
  let c : ℂ := (d : ℂ)⁻¹
  let W := V.map GaussianInt.toComplex
  have hdc : (d : ℂ) * c = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd)
  have hc : star c = c := by
    simp only [c, star_inv₀, star_natCast_complex]
  have hscale : c * c * (d : ℂ)^2 = 1 := by
    calc
      c * c * (d : ℂ)^2 = ((d : ℂ) * c)^2 := by ring
      _ = 1 := by rw [hdc, one_pow]
  have hGram : (c • W)ᴴ * (c • W) = 1 := by
    have hW : Wᴴ * W = (d : ℂ)^2 • 1 := (gaussianGram_map_iff V d).mp hV
    rw [Matrix.conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hW, smul_smul, hscale, one_smul]
  refine ⟨c • W, ⟨Matrix.mul_eq_one_comm.mp hGram, hGram⟩, ?_⟩
  rw [smul_smul, hdc, one_smul]

private theorem exists_integral_mixer {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hrat : ∀ i j, U i j ∈ gaussianRationalSubfield) :
    ∃ (d : ℕ) (V : Matrix (Fin n) (Fin n) GaussianInt), d ≠ 0 ∧
      Vᴴ * V = (d : GaussianInt)^2 • 1 ∧ V.map GaussianInt.toComplex = (d : ℂ) • U := by
  classical
  have hcoords (i j : Fin n) : ∃ p : ℚ × ℚ,
      (U i j).re = (p.1 : ℝ) ∧ (U i j).im = (p.2 : ℝ) := by
    rcases hrat i j with ⟨p, hp⟩
    exact ⟨p, congrArg Complex.re hp.symm, congrArg Complex.im hp.symm⟩
  choose p hp using hcoords
  let q : ((Fin n × Fin n) × Bool) → ℚ :=
    fun i => if i.2 then (p i.1.1 i.1.2).1 else (p i.1.1 i.1.2).2
  obtain ⟨d, hd, hz⟩ := Reformulations.NativeLinksB.exists_common_denominator q
  choose v hv using hz
  let V : Matrix (Fin n) (Fin n) GaussianInt :=
    Matrix.of fun i j => ⟨v ((i, j), true), v ((i, j), false)⟩
  have hmap : V.map GaussianInt.toComplex = (d : ℂ) • U := by
    apply Matrix.ext
    intro i j
    have hr : (d : ℝ) * (p i j).1 = v ((i, j), true) := by
      simpa [q] using congrArg (fun t : ℚ => (t : ℝ)) (hv ((i, j), true))
    have hi : (d : ℝ) * (p i j).2 = v ((i, j), false) := by
      simpa [q] using congrArg (fun t : ℚ => (t : ℝ)) (hv ((i, j), false))
    simp only [V, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    apply Complex.ext
    · rw [GaussianInt.toComplex_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero, (hp i j).1]
      exact hr.symm
    · rw [GaussianInt.toComplex_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        zero_mul, add_zero, (hp i j).2]
      exact hi.symm
  refine ⟨d, V, hd, (gaussianGram_map_iff V d).mpr ?_, hmap⟩
  rw [hmap, Matrix.conjTranspose_smul, star_natCast_complex, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hU.2, pow_two]

/-- The integer tests give the matching hull condition for the normalized mixer.
The conversion multiplies each projection by `Complex.normSq (GaussianInt.toComplex V.det)`. -/
theorem holds_iff_gaussianIntegerDeterminantTest {n d : ℕ} (a b : Fin n → GaussianInt)
    (V : Matrix (Fin n) (Fin n) GaussianInt) (U : Matrix (Fin n) (Fin n) ℂ)
    (hd : d ≠ 0) (hU : IsUnitary U) (hmap : V.map GaussianInt.toComplex = (d : ℂ) • U) :
    Holds (GaussianInt.toComplex ∘ a) (GaussianInt.toComplex ∘ b) U ↔
      GaussianIntegerDeterminantTest a b V := by
  let g := GaussianInt.toComplex
  let x := g ∘ a
  let y := g ∘ b
  have hdet : g V.det = (V.map g).det := g.map_det V
  have hne : g V.det ≠ 0 := by
    rw [hdet, hmap, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hd)) (det_ne_zero_of_unitary hU)
  have hM : (gaussianEntryMatrix a b V).map g =
      (diagonal x + U * diagonal y * Uᴴ) * V.map g := by
    change V.map g = (d : ℂ) • U at hmap
    rw [hmap, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_assoc (U * diagonal y),
      hU.2, Matrix.mul_one]
    apply Matrix.ext
    intro i j
    have hij : g (V i j) = (d : ℂ) * U i j :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hmap
    simp only [gaussianEntryMatrix, Matrix.map_apply, Matrix.of_apply, map_mul, map_add,
      Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      hij, x, y, Function.comp_apply]
    ring
  have hD : g (gaussianEntryMatrix a b V).det = determinantValue x y U * g V.det := by
    rw [g.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_mul, hdet, determinantValue]
  have hmatching (σ : Equiv.Perm (Fin n)) :
      g (gaussianMatching a b σ) = matchingProduct x y σ := by
    simp only [gaussianMatching, matchingProduct, map_prod, map_add, x, y, Function.comp_apply]
  have hI : g gaussianI = Complex.I := by
    simpa [g, gaussianI] using GaussianInt.toComplex_def' 0 1
  have hstar (z : GaussianInt) : g (star z) = star (g z) :=
    GaussianInt.toComplex_star z
  have hnormal (r s : Equiv.Perm (Fin n)) :
      g (gaussianI * star (gaussianMatching a b r - gaussianMatching a b s)) =
        Complex.I * star (matchingProduct x y r - matchingProduct x y s) := by
    rw [map_mul, hI, hstar, map_sub, hmatching, hmatching]
  have hsupport (k : GaussianInt) : gaussianIntegerSupport a b V k ↔
      ∃ σ : Equiv.Perm (Fin n), (g k * determinantValue x y U).re ≤ (g k * matchingProduct x y σ).re := by
    apply exists_congr
    intro σ
    let L := k * (star V.det * (gaussianEntryMatrix a b V).det)
    let R := k * ((star V.det * V.det) * gaussianMatching a b σ)
    change L.re ≤ R.re ↔ _
    have hL : g L = (Complex.normSq (g V.det) : ℂ) * (g k * determinantValue x y U) := by
      simp only [L, map_mul, hstar, hD, Complex.normSq_eq_conj_mul_self, Complex.star_def]
      ring
    have hR : g R = (Complex.normSq (g V.det) : ℂ) * (g k * matchingProduct x y σ) := by
      simp only [R, map_mul, hstar, hmatching, Complex.normSq_eq_conj_mul_self, Complex.star_def]
      ring
    have hcast : (L.re : ℝ) ≤ (R.re : ℝ) ↔ L.re ≤ R.re := Int.cast_le
    rw [← hcast, GaussianInt.to_real_re, GaussianInt.to_real_re]
    change (g L).re ≤ (g R).re ↔ _
    rw [hL, hR, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_left (Complex.normSq_pos.mpr hne)
  change Holds x y U ↔ _
  rw [holds_iff_axes_and_pair_normals x y U hU, GaussianIntegerDeterminantTest]
  simp only [hsupport, hnormal, map_neg, map_one, hI]
  constructor
  · rintro ⟨haxes, hnormals⟩
    exact ⟨haxes 1 (Or.inl rfl), haxes (-1) (Or.inr (Or.inl rfl)),
      haxes Complex.I (Or.inr (Or.inr (Or.inl rfl))),
      haxes (-Complex.I) (Or.inr (Or.inr (Or.inr rfl))), hnormals⟩
  · rintro ⟨hp, hn, hip, hin, hnormals⟩
    refine ⟨?_, hnormals⟩
    rintro k (rfl | rfl | rfl | rfl)
    · exact hp
    · exact hn
    · exact hip
    · exact hin

/-- In every order, it suffices to test Gaussian integer spectra and a Gaussian
integer matrix whose Gram matrix is `d² • 1` for some positive natural number `d`. -/
theorem mocIsTrue_iff_gaussianIntegerDeterminantTest :
    MOCIsTrue ↔ ∀ (n : ℕ) (a b : Fin n → GaussianInt)
      (d : ℕ) (V : Matrix (Fin n) (Fin n) GaussianInt), d ≠ 0 →
      Vᴴ * V = (d : GaussianInt)^2 • 1 → GaussianIntegerDeterminantTest a b V := by
  constructor
  · intro h n a b d V hd hGram
    obtain ⟨U, hU, hmap⟩ := exists_unitary_of_gaussianGram V d hd hGram
    exact (holds_iff_gaussianIntegerDeterminantTest a b V U hd hU hmap).mp (h n _ _ U hU)
  · intro h
    apply mocIsTrue_iff_gaussian_spectra_rational_mixer.mpr
    intro n a b U hU hrat
    obtain ⟨d, V, hd, hGram, hmap⟩ := exists_integral_mixer U hU hrat
    let x : Fin n → GaussianInt := fun i => ⟨(a i).1, (a i).2⟩
    let y : Fin n → GaussianInt := fun i => ⟨(b i).1, (b i).2⟩
    have hxy := (holds_iff_gaussianIntegerDeterminantTest x y V U hd hU hmap).mpr
      (h n x y d V hd hGram)
    simpa only [x, y, Function.comp_apply, GaussianInt.toComplex_def'] using hxy

end MOC
