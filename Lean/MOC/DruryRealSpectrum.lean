import MOC.DrurySpectralPartition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! The spectral conclusion of the two distinct real roots case of Drury's
Hermitian pencil argument. -/

open Matrix
open scoped Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluate a complex matrix characteristic polynomial at a scalar. -/
theorem eval_matrixCharpoly (A : Matrix ι ι ℂ) (z : ℂ) :
    A.charpoly.eval z = (z • (1 : Matrix ι ι ℂ) - A).det := by
  change (Polynomial.evalRingHom z) A.charmatrix.det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, smul_eq_mul]
  · simp [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.one_apply_ne hij,
      Matrix.smul_apply, smul_eq_mul]

/-- If every root of a Hermitian pencil at `z` lies on the real line or on
its multiple by `z`, it is a root at `1` or `z` times a root at `1`. -/
theorem hermitian_pencil_roots_partition (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ z : ℂ, z ≠ 0 → ∀ x : ℂ,
      (x • (1 : Matrix ι ι ℂ) - (A + z • B)).det = 0 →
        x = star x ∨ x / z = star (x / z))
    (z x : ℂ) (hz : z ≠ 0) (hx : (x • (1 : Matrix ι ι ℂ) - (A + z • B)).det = 0) :
    (x • (1 : Matrix ι ι ℂ) - (A + B)).det = 0 ∨
      ((x / z) • (1 : Matrix ι ι ℂ) - (A + B)).det = 0 := by
  let M : Matrix ι ι (ℂ[X]) := A.map Polynomial.C + (Polynomial.X : ℂ[X]) • B.map Polynomial.C
  let P := M.charpoly
  have hmap (w : ℂ) : P.map (Polynomial.evalRingHom w) = (A + w • B).charpoly := by
    change M.charpoly.map (Polynomial.evalRingHom w) = _
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j : 1
    simp only [M, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  have hstar (w t : ℂ) :
      ((star t) • (1 : Matrix ι ι ℂ) - (A + star w • B)).det =
        star ((t • (1 : Matrix ι ι ℂ) - (A + w • B)).det) := by
    have he : (t • (1 : Matrix ι ι ℂ) - (A + w • B))ᴴ =
        (star t) • (1 : Matrix ι ι ℂ) - (A + star w • B) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hA.eq, hB.eq]
    rw [← he, Matrix.det_conjTranspose]
  have hpair (w : ℂ) (hw : w ≠ 0) (t : ℂ)
      (ht : (P.map (Polynomial.evalRingHom w)).eval t = 0) :
      (P.map (Polynomial.evalRingHom (star w))).eval t = 0 ∨
        (P.map (Polynomial.evalRingHom (star w))).eval ((star w / w) * t) = 0 := by
    rw [hmap, eval_matrixCharpoly] at ht
    have hs := hstar w t
    rw [ht, star_zero] at hs
    rcases h w hw t ht with he | he
    · apply Or.inl
      rw [hmap, eval_matrixCharpoly]
      rw [he]
      exact hs
    · have he' : (star w / w) * t = star t := by
        rw [star_div₀] at he
        calc
          _ = star w * (t / w) := by simp only [div_eq_mul_inv]; ring
          _ = star w * (star t / star w) := by rw [he]
          _ = _ := by rw [mul_comm, div_mul_cancel₀ _ (star_ne_zero.mpr hw)]
      exact Or.inr (by rw [hmap, eval_matrixCharpoly, he']; exact hs)
  have he := polynomial_roots_specialize_of_conjugate_pairs P (Matrix.charpoly_monic M) hpair
    z 1 hz x (by rw [hmap, eval_matrixCharpoly]; exact hx)
  simpa only [hmap, eval_matrixCharpoly, one_smul, one_div, inv_mul_eq_div] using he

private theorem not_injective_div_of_two_scales {n : ℕ} (hn : 3 ≤ n)
    (a c : Fin n → ℂ) (ha : ∀ j, a j ≠ 0) (r s : ℂ)
    (h : ∀ i, ∃ j, c i = r * a j ∨ c i = s * a j) :
    ¬ Function.Injective (fun p : Fin n × Fin n => c p.1 / a p.2) := by
  classical
  choose j hj using h
  let f (i : Fin n) : Fin 2 := if c i = r * a (j i) then 0 else 1
  have hf (i : Fin n) : c i / a (j i) = ![r, s] (f i) := by
    by_cases hi : c i = r * a (j i)
    · simp [f, hi, mul_div_cancel_right₀, ha]
    · have he := (hj i).resolve_left hi
      rw [show f i = 1 from if_neg hi]
      change c i / a (j i) = s
      rw [he, mul_div_cancel_right₀ _ (ha (j i))]
  intro hinj
  have hfin : Function.Injective f := by
    intro i k hik
    have he : c i / a (j i) = c k / a (j k) := by rw [hf, hf, hik]
    exact congrArg Prod.fst (hinj (show (fun p : Fin n × Fin n => c p.1 / a p.2) (i, j i) =
      (fun p : Fin n × Fin n => c p.1 / a p.2) (k, j k) from he))
  have hcard := Fintype.card_le_of_injective f hfin
  simp only [Fintype.card_fin] at hcard
  omega

/-- The real-line root condition forces a collision among the ratios of the
eigenvalues of two fibers of a Hermitian pencil in order at least three. -/
theorem hermitian_pencil_ratios_not_injective {n : ℕ} (hn : 3 ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ z : ℂ, z ≠ 0 → ∀ x : ℂ,
      (x • (1 : Matrix (Fin n) (Fin n) ℂ) - (A + z • B)).det = 0 →
        x = star x ∨ x / z = star (x / z))
    (a c : Fin n → ℂ) (ha : ∀ j, a j ≠ 0) {r s : ℂ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hbase : ∀ x, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - (A + B)).det = 0 →
      ∃ j, x = a j)
    (hother : ∀ i, (c i • (1 : Matrix (Fin n) (Fin n) ℂ) - (r • A + s • B)).det = 0) :
    ¬ Function.Injective (fun p : Fin n × Fin n => c p.1 / a p.2) := by
  apply not_injective_div_of_two_scales hn a c ha r s
  intro i
  let z := s / r
  let x := c i / r
  have hz : z ≠ 0 := div_ne_zero hs hr
  have hmat : c i • (1 : Matrix (Fin n) (Fin n) ℂ) - (r • A + s • B) =
      r • (x • (1 : Matrix (Fin n) (Fin n) ℂ) - (A + z • B)) := by
    have hmul (y : ℂ) : r * (y / r) = y := by rw [mul_comm, div_mul_cancel₀ _ hr]
    dsimp only [x, z]
    simp only [smul_sub, smul_add, smul_smul, hmul]
  have hx : (x • (1 : Matrix (Fin n) (Fin n) ℂ) - (A + z • B)).det = 0 := by
    have hi := hother i
    rw [hmat, Matrix.det_smul] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ hr)
  rcases hermitian_pencil_roots_partition A B hA hB h z x hz hx with h₁ | h₂
  · obtain ⟨j, hj⟩ := hbase x h₁
    exact ⟨j, Or.inl (by rw [mul_comm, ← hj, div_mul_cancel₀ _ hr])⟩
  · have he : x / z = c i / s := by
      dsimp only [x, z]
      field_simp [hr, hs] <;> ring
    rw [he] at h₂
    obtain ⟨j, hj⟩ := hbase (c i / s) h₂
    exact ⟨j, Or.inr (by rw [mul_comm, ← hj, div_mul_cancel₀ _ hs])⟩

private theorem polynomial_eval_constant_of_real_values (p : ℂ[X])
    (h : ∀ z : ℂ, star (p.eval z) = p.eval z) (z : ℂ) : p.eval z = p.eval 0 := by
  have hdeg : p.natDegree ≤ 0 := by
    by_contra hdeg
    have hp : 0 < p.natDegree := lt_of_not_ge hdeg
    let q := p - Polynomial.C Complex.I
    have hq : q.degree ≠ 0 := by
      intro he
      have hn : q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some he
      rw [show q.natDegree = p.natDegree from Polynomial.natDegree_sub_C] at hn
      exact hp.ne' hn
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hq
    have he : p.eval x = Complex.I := by
      simpa only [q, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] using hx
    have hs := h x
    rw [he] at hs
    have him := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im, Complex.I_im] at him
    norm_num at him
  have he (x : ℂ) : p.eval x = p.coeff 0 :=
    (congrArg (Polynomial.eval x) (Polynomial.eq_C_of_natDegree_le_zero hdeg)).trans
      Polynomial.eval_C
  exact (he z).trans (he 0).symm

private theorem polynomial_map_star_eq_of_real_roots (p : ℂ[X]) (hp : p.Monic)
    (h : ∀ x : ℂ, p.eval x = 0 → star x = x) : p.map (starRingEnd ℂ) = p := by
  have he : p = (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod := by
    calc
      p = Polynomial.C p.leadingCoeff * (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
        Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits p)
      _ = _ := by rw [hp.leadingCoeff, Polynomial.C_1, one_mul]
  calc
    _ = ((p.roots.map fun a => Polynomial.X - Polynomial.C a).prod).map (starRingEnd ℂ) :=
      congrArg (fun q : ℂ[X] => q.map (starRingEnd ℂ)) he
    _ = _ := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      have hm : p.roots.map ((fun q : ℂ[X] => q.map (starRingEnd ℂ)) ∘
          fun a => Polynomial.X - Polynomial.C a) = p.roots.map (fun a => Polynomial.X - Polynomial.C a) := by
        apply Multiset.map_congr rfl
        intro a ha
        simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          starRingEnd_apply, h a ((Polynomial.mem_roots hp.ne_zero).mp ha)]
      rw [hm, ← he]

/-- A monic complex polynomial family whose roots stay real for every complex
parameter has constant coefficients. -/
theorem polynomial_family_constant_of_real_roots (P : Polynomial (ℂ[X])) (hP : P.Monic)
    (h : ∀ z x : ℂ, (P.map (Polynomial.evalRingHom z)).eval x = 0 → star x = x)
    (z : ℂ) : P.map (Polynomial.evalRingHom z) = P.map (Polynomial.evalRingHom 0) := by
  ext n : 1
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  apply polynomial_eval_constant_of_real_values
  intro w
  have he := polynomial_map_star_eq_of_real_roots (P.map (Polynomial.evalRingHom w))
    (hP.map _) (h w)
  simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, starRingEnd_apply] using
    congrArg (fun q : ℂ[X] => q.coeff n) he

/-- An affine complex matrix family with real spectrum at every complex
parameter has the characteristic polynomial of its constant term. -/
theorem charpoly_affine_constant_of_real_roots (A B : Matrix ι ι ℂ)
    (h : ∀ z x : ℂ, (x • (1 : Matrix ι ι ℂ) - (A + z • B)).det = 0 → star x = x)
    (z : ℂ) : (A + z • B).charpoly = A.charpoly := by
  let M : Matrix ι ι (ℂ[X]) := A.map Polynomial.C + (Polynomial.X : ℂ[X]) • B.map Polynomial.C
  let P := M.charpoly
  have hmap (w : ℂ) : P.map (Polynomial.evalRingHom w) = (A + w • B).charpoly := by
    change M.charpoly.map (Polynomial.evalRingHom w) = _
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j : 1
    simp only [M, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  have hreal (w x : ℂ) (hx : (P.map (Polynomial.evalRingHom w)).eval x = 0) : star x = x := by
    rw [hmap, eval_matrixCharpoly] at hx
    exact h w x hx
  have he := polynomial_family_constant_of_real_roots P (Matrix.charpoly_monic M) hreal z
  simpa only [hmap, zero_smul, add_zero] using he

end

end MOC
