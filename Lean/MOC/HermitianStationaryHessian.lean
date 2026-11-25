import MOC.DeterminantSecondVariation
import MOC.HermitianStationarySwap

/-! The support Hessian for a Hermitian summand on its unitary orbit. -/

open Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The inverse and the first two commutators give the second variation
of determinant support along a unitary conjugation. -/
theorem hermitian_orbit_hessian_nonpos (H B K : Matrix ι ι ℂ) (θ : ℂ)
    (hK : Kᴴ = -K) (hm : (H + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ (θ * (H + B).det).re) :
    let M := H + B
    let N := M⁻¹
    let A := K * H - H * K
    let D := K * A - A * K
    (θ * M.det *
      ((N * D).trace + (N * A).trace ^ 2 - ((N * A) * (N * A)).trace)).re ≤ 0 := by
  intro M N A D
  let V (t : ℝ) := NormedSpace.exp ℝ (t • K)
  let W (t : ℝ) := NormedSpace.exp ℝ (t • (-K))
  let T (t : ℝ) := N * (V t * H * W t + B)
  let T' (t : ℝ) := N * (V t * K * H * W t + V t * H * (W t * (-K)))
  have hunit (t : ℝ) : IsUnitary (V t) := by
    have hs : t • K ∈ skewAdjoint (Matrix ι ι ℂ) := by
      rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        star_trivial, hK, smul_neg]
    have he := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hs)
    exact ⟨he.2, he.1⟩
  have hstar (t : ℝ) : (V t)ᴴ = W t := by
    change (NormedSpace.exp ℝ (t • K))ᴴ = NormedSpace.exp ℝ (t • (-K))
    rw [← Matrix.exp_conjTranspose ℝ, Matrix.conjTranspose_smul, star_trivial, hK]
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hm
  have hV (t : ℝ) : HasDerivAt V (V t * K) t := hasDerivAt_exp_smul_const K t
  have hW (t : ℝ) : HasDerivAt W (W t * (-K)) t := hasDerivAt_exp_smul_const (-K) t
  have hT (t : ℝ) : HasDerivAt T (T' t) t := by
    simpa only [T, T', Matrix.mul_assoc] using
      ((((hV t).mul_const H).mul (hW t)).add_const B).const_mul N
  have hT₀ : T 0 = 1 := by
    simpa only [T, V, W, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one] using
      M.nonsing_inv_mul hM
  have hT'₀ : T' 0 = N * A := by
    simp only [T', V, W, A, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_neg, sub_eq_add_neg]
  have hV₀ : HasDerivAt V K 0 := by
    simpa only [V, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using hV 0
  have hW₀ : HasDerivAt W (-K) 0 := by
    simpa only [W, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using hW 0
  have hT' : HasDerivAt T' (N * D) 0 := by
    have h₁ := (((hV₀.mul_const K).mul_const H).mul hW₀)
    have h₂ := (hV₀.mul_const H).mul (hW₀.mul_const (-K))
    convert (h₁.add h₂).const_mul N using 1
    simp only [V, W, D, A, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  have hdet (t : ℝ) : (V t * H * W t + B).det = M.det * (T t).det := by
    rw [← Matrix.det_mul]
    dsimp only [T, N]
    rw [← Matrix.mul_assoc, M.mul_nonsing_inv hM, Matrix.one_mul]
  let f (t : ℝ) := ((θ * M.det) * (T t).det).re
  have hfmax : IsLocalMax f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have ht := hmax (V t) (hunit t)
    rw [hstar, hdet, ← mul_assoc] at ht
    simpa only [f, hT₀, Matrix.det_one, mul_one] using ht
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), (T t).det ≠ 0 := by
    have hne : (T 0).det ≠ 0 := by simp [hT₀]
    exact (hasDerivAt_det_of_ne_zero (hT 0) hne).continuousAt.eventually_ne hne
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t := by
    filter_upwards [hn] with t ht
    have hd := (hasDerivAt_det_of_ne_zero (hT t) ht).const_mul (θ * M.det)
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd).differentiableAt
  have heq : deriv f =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ((θ * M.det) * deriv (fun s => (T s).det) t).re) := by
    filter_upwards [hn] with t ht
    have hd := hasDerivAt_det_of_ne_zero (hT t) ht
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (hd.differentiableAt.hasDerivAt.const_mul (θ * M.det))).deriv
  have hsecond := hasDerivAt_deriv_det_of_eq_one (Filter.Eventually.of_forall hT) hT₀ hT'
  rw [hT'₀] at hsecond
  have hp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hsecond.const_mul (θ * M.det))
  exact second_derivative_nonpos_of_local_max hfmax hf (hp.congr_of_eventuallyEq heq)

private theorem linear_eq_zero_of_quadratic_nonpos {a b : ℝ}
    (h : ∀ t : ℝ, t * a + t ^ 2 * b ≤ 0) : a = 0 := by
  by_contra ha
  let c := |b| + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : 0 < c + b := by
    dsimp [c]
    linarith only [neg_abs_le b]
  have he : (a / c) * a + (a / c) ^ 2 * b = (a / c) ^ 2 * (c + b) := by
    field_simp [hc.ne'] <;> ring
  have hh := h (a / c)
  rw [he] at hh
  exact (not_lt_of_ge hh)
    (mul_pos (sq_pos_of_ne_zero (div_ne_zero ha hc.ne')) hp)

set_option maxHeartbeats 700000 in
/-- A flat orbit direction has zero mixed determinant curvature. When its
inverse trace and the mixed acceleration term vanish, only the inverse
quadratic term remains. -/
theorem hermitian_orbit_flat_direction_trace_zero (H B K L : Matrix ι ι ℂ)
    (θ : ℂ) (hK : Kᴴ = -K) (hL : Lᴴ = -L) (hm : (H + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ (θ * (H + B).det).re) :
    let M := H + B
    let N := M⁻¹
    let η := θ * M.det
    let A := K * H - H * K
    let D := L * H - H * L
    (N * A).trace = 0 →
    (η * ((N * (K * A - A * K)).trace - ((N * A) * (N * A)).trace)).re = 0 →
    (η * (N * (K * D - D * K + (L * A - A * L))).trace).re = 0 →
    (η * ((N * A) * (N * D)).trace).re = 0 := by
  intro M N η A D htr hflat hacc
  let u := N * A
  let v := N * D
  let q := (η * ((N * (L * D - D * L)).trace + v.trace ^ 2 - (v * v).trace)).re
  have hpoly (t : ℝ) : t * (-2 * (η * (u * v).trace).re) + t ^ 2 * q ≤ 0 := by
    let s : ℂ := t
    let E := K + s • L
    have hE : Eᴴ = -E := by
      simp only [E, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hK, hL, s,
        Complex.star_def, Complex.conj_ofReal, smul_neg, neg_add]
    have hvel : E * H - H * E = A + s • D := by
      simp only [E, A, D, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        smul_sub]
      abel
    have hacc' : E * (A + s • D) - (A + s • D) * E =
        (K * A - A * K) + s • (K * D - D * K + (L * A - A * L)) +
          s ^ 2 • (L * D - D * L) := by
      simp only [E, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        pow_two, MulAction.mul_smul, smul_sub, smul_add]
      abel
    have h := hermitian_orbit_hessian_nonpos H B E θ hE hm hmax
    dsimp only at h
    change (η * ((N * (E * (E * H - H * E) - (E * H - H * E) * E)).trace +
      (N * (E * H - H * E)).trace ^ 2 -
      ((N * (E * H - H * E)) * (N * (E * H - H * E))).trace)).re ≤ 0 at h
    rw [hvel, hacc'] at h
    have htrace : u.trace = 0 := htr
    have hcyc : (v * u).trace = (u * v).trace := Matrix.trace_mul_comm _ _
    have hcomplex :
        η * ((N * ((K * A - A * K) + s • (K * D - D * K + (L * A - A * L)) +
            s ^ 2 • (L * D - D * L))).trace + (N * (A + s • D)).trace ^ 2 -
          ((N * (A + s • D)) * (N * (A + s • D))).trace) =
        η * ((N * (K * A - A * K)).trace - (u * u).trace) +
          s * (η * (N * (K * D - D * K + (L * A - A * L))).trace) -
          s * (2 * (η * (u * v).trace)) +
          s ^ 2 * (η * ((N * (L * D - D * L)).trace + v.trace ^ 2 - (v * v).trace)) := by
      have ha : N * (A + s • D) = u + s • v := by
        simp only [u, v, Matrix.mul_add, Matrix.mul_smul]
      rw [ha]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
        Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, htrace, hcyc]
      ring
    rw [hcomplex] at h
    have hflat' : (η * ((N * (K * A - A * K)).trace - (u * u).trace)).re = 0 := hflat
    simp only [Complex.add_re, Complex.sub_re, s, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, hflat', hacc, mul_zero, add_zero, zero_add, zero_sub] at h
    have hn : (2 * (η * (u * v).trace)).re = 2 * (η * (u * v).trace).re := by
      simpa using (Complex.re_ofReal_mul (2 : ℝ) (η * (u * v).trace))
    rw [hn] at h
    change -(t * (2 * (η * (u * v).trace).re)) + t ^ 2 * q ≤ 0 at h
    convert h using 1 <;> ring
  have hz := linear_eq_zero_of_quadratic_nonpos hpoly
  linarith only [hz]

private theorem im_trace_mul_hermitian (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : ((A * B).trace).im = 0 := by
  have he := congrArg Complex.im (Matrix.trace_conjTranspose (A * B))
  rw [Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm B A,
    Complex.star_def, Complex.conj_im] at he
  linarith only [he]

/-- A flat direction forces the Hermitian part of its inverse-quadratic
variation to commute with the original Hermitian summand. -/
theorem hermitian_orbit_flat_direction_commutes (H B K T : Matrix ι ι ℂ)
    (θ γ : ℂ) (hH : H.IsHermitian) (hK : Kᴴ = -K) (hT : T.IsHermitian)
    (hm : (H + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ (θ * (H + B).det).re) :
    let M := H + B
    let N := M⁻¹
    let η := θ * M.det
    let A := K * H - H * K
    (N * A).trace = 0 →
    (η * ((N * (K * A - A * K)).trace - ((N * A) * (N * A)).trace)).re = 0 →
    (∀ L : Matrix ι ι ℂ, Lᴴ = -L →
      let D := L * H - H * L
      (η * (N * (K * D - D * K + (L * A - A * L))).trace).re = 0) →
    N * A * N = γ • T → (η * γ).re ≠ 0 → Commute H T := by
  intro M N η A htr hflat hacc hquad hγ
  have ht := conjTranspose_eq_of_real_trace_mul_skew_eq_zero (H * T - T * H) (by
    intro L hL
    let D := L * H - H * L
    have hD : D.IsHermitian := by
      show Dᴴ = D
      simp only [D, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq, hL,
        Matrix.neg_mul, Matrix.mul_neg, neg_sub_neg]
    have he := hermitian_orbit_flat_direction_trace_zero H B K L θ hK hL hm hmax
      htr hflat (hacc L hL)
    change (η * ((N * A) * (N * D)).trace).re = 0 at he
    rw [← Matrix.mul_assoc (N * A), hquad, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      ← mul_assoc, Complex.mul_re, im_trace_mul_hermitian T D hT hD, mul_zero, sub_zero] at he
    have hz := (mul_eq_zero.mp he).resolve_left hγ
    have hc : ((H * T - T * H) * L).trace = (T * D).trace := by
      simp only [D, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
      rw [← Matrix.trace_mul_cycle T L H, Matrix.mul_assoc T L H, Matrix.mul_assoc T H L]
    rw [hc, hz])
  have hs : (H * T - T * H)ᴴ = -(H * T - T * H) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq, hT.eq, neg_sub]
  have hz : (2 : ℂ) • (H * T - T * H) = 0 := by
    calc
      _ = (H * T - T * H)ᴴ + (H * T - T * H) := by rw [two_smul, ht]
      _ = 0 := by rw [hs, neg_add_cancel]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

private theorem diagonal_commute_entry_zero (h : ι → ℝ) (hh : Function.Injective h)
    {C : Matrix ι ι ℂ} (hc : Commute (diagonal fun i => (h i : ℂ)) C)
    {i j : ι} (hij : i ≠ j) : C i j = 0 := by
  have he := congrArg (fun T : Matrix ι ι ℂ => T i j) hc.eq
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (C i j)] at he
  by_contra hn
  exact hij (hh (Complex.ofReal_injective (mul_right_cancel₀ hn he)))

private theorem trace_add_commutator_pairing_zero (Z K A L D : Matrix ι ι ℂ)
    (hK : Commute Z K) (hA : Commute Z A) :
    (Z * (K * D - D * K + (L * A - A * L))).trace = 0 := by
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
  have h₁ : (Z * (K * D)).trace = (Z * (D * K)).trace := by
    rw [← Matrix.mul_assoc Z K D, hK.eq, ← Matrix.trace_mul_cycle Z D K,
      Matrix.mul_assoc]
  have h₂ : (Z * (L * A)).trace = (Z * (A * L)).trace := by
    rw [← Matrix.mul_assoc Z L A, Matrix.trace_mul_cycle, ← hA.eq, Matrix.mul_assoc]
  simp only [h₁, h₂, sub_self, add_zero]

private theorem scaled_real_trace_eq_half_adjoint
    (Z A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (Z * A).trace.re = ((Z + Zᴴ) * A).trace.re / 2 := by
  have he := congrArg Complex.re (Matrix.trace_conjTranspose (Z * A))
  rw [Matrix.conjTranspose_mul, hA.eq, Matrix.trace_mul_comm A Zᴴ,
    Complex.star_def, Complex.conj_re] at he
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, he]
  ring

private theorem matrix_unit_sandwich_entry (C D : Matrix ι ι ℂ)
    (i j k l : ι) (z : ℂ) :
    (C * stdBasisMatrix i j z * D) k l = C k i * z * D j l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.StdBasisMatrix.mul_right_apply_same]
  · intro r _ hr
    rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := hr), zero_mul]
  · simp

private theorem trace_mul_matrix_unit (C : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    (C * stdBasisMatrix i j z).trace = C j i * z := by
  rw [Matrix.trace, Finset.sum_eq_single j]
  · rw [Matrix.diag_apply, Matrix.StdBasisMatrix.mul_right_apply_same]
  · intro r _ hr
    rw [Matrix.diag_apply, Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := hr)]
  · simp

private theorem some_column_entry_nonzero (C : Matrix ι ι ℂ)
    (hC : IsUnit C.det) (i : ι) : ∃ k, C k i ≠ 0 := by
  by_contra! hn
  have he := congrArg (fun T : Matrix ι ι ℂ => T i i) (C.nonsing_inv_mul hC)
  simp only [Matrix.mul_apply, hn, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq,
    zero_ne_one] at he

private theorem not_commute_both_pair_phases (h : ι → ℝ) (C : Matrix ι ι ℂ)
    (hh : Function.Injective h) (hC : C.IsHermitian) (hCu : IsUnit C.det) {i j : ι} (hij : i ≠ j)
    (hc : ∀ z : ℂ, Commute (diagonal fun k => (h k : ℂ))
      (C * (stdBasisMatrix i j z + stdBasisMatrix j i (star z)) * C)) : False := by
  have hprod (r s : ι) (hrs : r ≠ s) : C r i * C j s = 0 := by
    have h₁ := diagonal_commute_entry_zero h hh (hc 1) hrs
    have h₂ := diagonal_commute_entry_zero h hh (hc Complex.I) hrs
    have hm (z : ℂ) :
        (C * (stdBasisMatrix i j z + stdBasisMatrix j i (star z)) * C) r s =
          C r i * z * C j s + C r j * star z * C i s := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, matrix_unit_sandwich_entry]
    rw [hm, star_one, mul_one, mul_one] at h₁
    rw [hm, Complex.star_def, Complex.conj_I] at h₂
    have h₂' : Complex.I * (C r i * C j s - C r j * C i s) = 0 := by
      linear_combination h₂
    have hd := (mul_eq_zero.mp h₂').resolve_left Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * (h₁ + hd)
  obtain ⟨k, hk⟩ := some_column_entry_nonzero C hCu i
  have hjl (l : ι) (hl : l ≠ k) : C j l = 0 :=
    (mul_eq_zero.mp (hprod k l hl.symm)).resolve_left hk
  have hjcol (l : ι) (hl : l ≠ k) : C l j = 0 := by
    have he := congrArg (fun T : Matrix ι ι ℂ => T l j) hC.eq
    simpa only [Matrix.conjTranspose_apply, hjl l hl, star_zero] using he.symm
  have hkj : C k j ≠ 0 := by
    obtain ⟨l, hl⟩ := some_column_entry_nonzero C hCu j
    by_cases e : l = k
    · rwa [e] at hl
    · exact (hl (hjcol l e)).elim
  have hjk : C j k ≠ 0 := by
    intro he
    have hk' := congrArg (fun T : Matrix ι ι ℂ => T k j) hC.eq
    exact hkj (by simpa only [Matrix.conjTranspose_apply, he, star_zero] using hk'.symm)
  have hicol (l : ι) (hl : l ≠ k) : C l i = 0 :=
    (mul_eq_zero.mp (hprod l k hl)).resolve_right hjk
  have hleft (r s : ι) (hs : ∀ l, l ≠ k → C l s = 0) :
      (C⁻¹ * C) r s = C⁻¹ r k * C k s := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · intro l _ hl
      rw [hs l hl, mul_zero]
    · simp
  have hzero : C⁻¹ i k = 0 := by
    have he := hleft i j hjcol
    rw [C.nonsing_inv_mul hCu, Matrix.one_apply_ne hij] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hkj
  have he := hleft i i hicol
  rw [C.nonsing_inv_mul hCu, Matrix.one_apply_eq, hzero, zero_mul] at he
  exact one_ne_zero he

set_option maxHeartbeats 1000000 in
/-- A pair of stationary inverse columns cannot form an isotropic flat
pair at a support maximum. The row and column identities are the ones
obtained on the kernel of the scaled inverse's Hermitian part. -/
theorem hermitian_orbit_inverse_pair_nonflat (h : ι → ℝ) (B C : Matrix ι ι ℂ)
    (θ c : ℂ) (hh : Function.Injective h) (hC : C.IsHermitian) (hCu : IsUnit C.det)
    {i j : ι} (hij : i ≠ j) (hCi : C i i = 0) (hCij : C i j = 0) (hCji : C j i = 0) :
    let H := diagonal fun k => (h k : ℂ)
    let M := H + B
    let N := M⁻¹
    let η := θ * M.det
    M.det ≠ 0 →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ η.re) →
    star (η * c) = -(η * c) → (η * c ^ 2).re ≠ 0 →
    (∀ k, N k i = c * C k i) → (∀ k, N k j = c * C k j) →
    (∀ k, N i k = c * C i k) → (∀ k, N j k = c * C j k) → False := by
  intro H M N η hm hmax hηc hγ hci hcj hri hrj
  let Z := η • N
  let X := Z + Zᴴ
  have hH : H.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro k
    simp [isSelfAdjoint_iff, Complex.star_def]
  have hx (r : ι) (hc : ∀ k, N k r = c * C k r) (hr : ∀ k, N r k = c * C r k) :
      (∀ k, X k r = 0) ∧ (∀ k, X r k = 0) := by
    have hcol (k : ι) : star (C r k) = C k r :=
      congrArg (fun T : Matrix ι ι ℂ => T k r) hC.eq
    have hrow (k : ι) : star (C k r) = C r k :=
      congrArg (fun T : Matrix ι ι ℂ => T r k) hC.eq
    constructor
    · intro k
      simp only [X, Z, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
        smul_eq_mul, hc, hr, ← mul_assoc, star_mul', hηc, hcol, neg_mul, add_neg_cancel]
    · intro k
      simp only [X, Z, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
        smul_eq_mul, hc, hr, ← mul_assoc, star_mul', hηc, hrow, neg_mul, add_neg_cancel]
  obtain ⟨hxi, hix⟩ := hx i hci hri
  obtain ⟨hxj, hjx⟩ := hx j hcj hrj
  have hE (r s : ι) (z : ℂ) (hc : ∀ k, X k r = 0) (hr : ∀ k, X s k = 0) :
      Commute X (stdBasisMatrix r s z) := by
    show X * stdBasisMatrix r s z = stdBasisMatrix r s z * X
    have hl : X * stdBasisMatrix r s z = 0 := by
      ext k l : 1
      by_cases he : l = s
      · subst l
        rw [Matrix.StdBasisMatrix.mul_right_apply_same, hc, zero_mul, Matrix.zero_apply]
      · rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := he), Matrix.zero_apply]
    have hr' : stdBasisMatrix r s z * X = 0 := by
      ext k l : 1
      by_cases he : k = r
      · subst k
        rw [Matrix.StdBasisMatrix.mul_left_apply_same, hr, mul_zero, Matrix.zero_apply]
      · rw [Matrix.StdBasisMatrix.mul_left_apply_of_ne _ _ _ _ _ he, Matrix.zero_apply]
    rw [hl, hr']
  have hReal (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
      (η * (N * A).trace).re = (X * A).trace.re / 2 := by
    simpa only [X, Z, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using
      scaled_real_trace_eq_half_adjoint Z A hA
  apply not_commute_both_pair_phases h C hh hC hCu hij
  intro z
  let E := stdBasisMatrix i j z
  let F := stdBasisMatrix j i (star z)
  let K := E - F
  let A := K * H - H * K
  let d : ℂ := (h j : ℂ) - h i
  let T := C * A * C
  have hK : Kᴴ = -K := by
    simp only [K, E, F, Matrix.conjTranspose_sub, Matrix.conjTranspose_stdBasisMatrix,
      star_star, neg_sub]
  have hA : A.IsHermitian := by
    show Aᴴ = A
    simp only [A, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq, hK,
      Matrix.mul_neg, Matrix.neg_mul, neg_sub_neg]
  have hT : T.IsHermitian := by
    show Tᴴ = T
    simp only [T, Matrix.conjTranspose_mul, hC.eq, hA.eq, Matrix.mul_assoc]
  have hAeq : A = d • (E + F) := by
    have hunit (r s : ι) (u : ℂ) :
        stdBasisMatrix r s u * H - H * stdBasisMatrix r s u =
          ((h s : ℂ) - h r) • stdBasisMatrix r s u := by
      ext k l : 1
      simp only [H, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.stdBasisMatrix, Matrix.of_apply]
      by_cases hk : r = k <;> by_cases hl : s = l <;> simp [hk, hl] <;> ring
    have hF : F * H - H * F = -d • F := by
      rw [show -d = (h i : ℂ) - h j by dsimp [d]; ring]
      exact hunit j i (star z)
    calc
      A = (E * H - H * E) - (F * H - H * F) := by
        simp only [A, K, Matrix.mul_sub, Matrix.sub_mul]
        abel
      _ = _ := by rw [show E * H - H * E = d • E from hunit i j z, hF,
        neg_smul, sub_neg_eq_add, smul_add]
  have hXK : Commute X K := (hE i j z hxi hjx).sub_right (hE j i (star z) hxj hix)
  have hXA : Commute X A := by
    rw [hAeq]
    have he := ((hE i j z hxi hjx).add_right (hE j i (star z) hxj hix)).eq
    change X * (d • (E + F)) = (d • (E + F)) * X
    rw [Matrix.mul_smul, Matrix.smul_mul, show X * (E + F) = (E + F) * X from he]
  have htr : (N * A).trace = 0 := by
    rw [hAeq, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add]
    simp only [E, F, trace_mul_matrix_unit, hcj i, hci j, hCij, hCji, mul_zero, zero_mul,
      add_zero, smul_zero]
  have hquad : N * A * N = c ^ 2 • T := by
    simp only [T, hAeq, E, F, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
    ext k l : 1
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, matrix_unit_sandwich_entry,
      hci, hcj, hri, hrj]
    ring
  have hTij : T i j = 0 ∧ T j i = 0 := by
    simp only [T, hAeq, E, F, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, matrix_unit_sandwich_entry,
      hCi, hCij, hCji, zero_mul, mul_zero, add_zero, and_self]
  have hTA : (T * A).trace = 0 := by
    rw [hAeq, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add]
    simp only [E, F, trace_mul_matrix_unit, hTij.1, hTij.2, zero_mul, add_zero, smul_zero]
  have hcommHermitian (L Y : Matrix ι ι ℂ) (hL : Lᴴ = -L) (hY : Y.IsHermitian) :
      (L * Y - Y * L).IsHermitian := by
    show (L * Y - Y * L)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hL, hY.eq,
      Matrix.mul_neg, Matrix.neg_mul, neg_sub_neg]
  have hflat : (η * ((N * (K * A - A * K)).trace - ((N * A) * (N * A)).trace)).re = 0 := by
    have hzero : (X * (K * A - A * K)).trace = 0 := by
      simpa only [Matrix.zero_mul, Matrix.mul_zero, sub_self, add_zero] using
        trace_add_commutator_pairing_zero X K A 0 A hXK hXA
    have hterm : ((N * A) * (N * A)).trace = 0 := by
      rw [← Matrix.mul_assoc (N * A), hquad, Matrix.smul_mul, Matrix.trace_smul, hTA, smul_zero]
    rw [hterm, sub_zero, hReal _ (hcommHermitian K A hK hA), hzero, Complex.zero_re, zero_div]
  have hacc (L : Matrix ι ι ℂ) (hL : Lᴴ = -L) :
      let D := L * H - H * L
      (η * (N * (K * D - D * K + (L * A - A * L))).trace).re = 0 := by
    intro D
    have hD : D.IsHermitian := hcommHermitian L H hL hH
    rw [hReal _ ((hcommHermitian K D hK hD).add (hcommHermitian L A hL hA)),
      trace_add_commutator_pairing_zero X K A L D hXK hXA, Complex.zero_re, zero_div]
  have hcomm := hermitian_orbit_flat_direction_commutes H B K T θ (c ^ 2) hH hK hT hm hmax
    htr hflat hacc hquad hγ
  have hδ : d ≠ 0 := sub_ne_zero.mpr (fun he => hij (hh (Complex.ofReal_injective he.symm)))
  have hself := hcomm.eq
  change H * T = T * H at hself
  simp only [T, hAeq, Matrix.mul_smul, Matrix.smul_mul] at hself
  exact smul_right_injective _ hδ hself

set_option maxHeartbeats 1500000 in
/-- At a positive support maximum with invertible imaginary part, two zero
diagonal entries of the Hermitian part of the scaled inverse have opposite
signs for the corresponding diagonal entries of the inverse imaginary
part. This applies to mixed imaginary signs. -/
theorem hermitian_orbit_zero_inverse_diagonal_pair (h : ι → ℝ) (R W : Matrix ι ι ℂ)
    (θ : ℂ) (hh : Function.Injective h) (hR : R.IsHermitian) (hW : W.IsHermitian)
    (hRW : Commute R W) (hWu : IsUnit W.det) {i j : ι} (hij : i ≠ j) :
    let H := diagonal fun k => (h k : ℂ)
    let B := R + Complex.I • W
    let M := H + B
    let N := M⁻¹
    let η := θ * M.det
    let C := W⁻¹
    0 < η.re →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ η.re) →
    (η * N i i).re = 0 → (η * N j j).re = 0 → (C i i).re * (C j j).re < 0 := by
  intro H B M N η C ha hmax hxi hxj
  let Z := η • N
  let X := Z + Zᴴ
  let a : ℂ := η.re
  let c := -(Complex.I * a) / η
  have hη : η ≠ 0 := fun he => by simp [he] at ha
  have ha' : a ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hm : M.det ≠ 0 := fun he => hη (by simp [η, he])
  have hMu := isUnit_iff_ne_zero.mpr hm
  have hH : H.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro k
    simp [isSelfAdjoint_iff, Complex.star_def]
  have hC : C.IsHermitian := hW.inv
  have hCu : IsUnit C.det := W.isUnit_nonsing_inv_det hWu
  have hCW : C * W = 1 := W.nonsing_inv_mul hWu
  have hWC : W * C = 1 := W.mul_nonsing_inv hWu
  have hRC : (R * C).IsHermitian := by
    show (R * C)ᴴ = R * C
    rw [Matrix.conjTranspose_mul, hR.eq, hC.eq]
    calc
      C * R = C * (R * (W * C)) := by rw [hWC, Matrix.mul_one]
      _ = C * (W * (R * C)) := by rw [← Matrix.mul_assoc R W C, hRW.eq, Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc C W (R * C), hCW, Matrix.one_mul]
  have hmax' (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      (θ * (B + V * H * Vᴴ).det).re ≤ (θ * (B + H).det).re := by
    simpa only [add_comm B, M, η] using hmax V hV
  have hstat := support_maximum_inverse_commutator B H θ (by simpa only [add_comm B H] using hm) hmax'
  dsimp only at hstat
  rw [add_comm B H] at hstat
  have hZX : (H * Z - Z * H)ᴴ = H * Z - Z * H := by
    simpa only [Z, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub] using hstat
  have hX : Commute H X := by
    have he : Zᴴ * H - H * Zᴴ = H * Z - Z * H := by
      simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq] using hZX
    change H * X = X * H
    simp only [X, Matrix.mul_add, Matrix.add_mul]
    calc
      _ = (H * Z - Z * H) + (H * Zᴴ + Z * H) := by abel
      _ = _ := by rw [← he]; abel
  have hXr (r : ι) (hr : (η * N r r).re = 0) :
      (∀ k, X k r = 0) ∧ (∀ k, X r k = 0) := by
    have hd : X r r = 0 := by
      simp only [X, Z, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
        smul_eq_mul, Complex.star_def, Complex.add_conj, hr, mul_zero, Complex.ofReal_zero]
    constructor
    · intro k
      by_cases he : k = r
      · simpa only [he] using hd
      · exact diagonal_commute_entry_zero h hh hX he
    · intro k
      by_cases he : r = k
      · simpa only [← he] using hd
      · exact diagonal_commute_entry_zero h hh hX he
  have hMstar : Mᴴ = M - (2 * Complex.I) • W := by
    simp only [M, B, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH.eq, hR.eq, hW.eq,
      Complex.star_def, Complex.conj_I, neg_smul, two_mul, add_smul]
    abel
  have hMZ : M * Z = η • (1 : Matrix ι ι ℂ) := by
    change M * (η • M⁻¹) = _
    rw [Matrix.mul_smul, M.mul_nonsing_inv hMu]
  have hMZstar : Mᴴ * Zᴴ = star η • (1 : Matrix ι ι ℂ) := by
    have he : Mᴴ * Nᴴ = 1 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
        congrArg Matrix.conjTranspose (M.nonsing_inv_mul hMu)
    change Mᴴ * (η • N)ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, he]
  have hXcalc : Mᴴ * X = (2 * a) • (1 : Matrix ι ι ℂ) - (2 * Complex.I) • (W * Z) := by
    change Mᴴ * (Z + Zᴴ) = _
    rw [Matrix.mul_add, hMZstar, hMstar, Matrix.sub_mul, Matrix.smul_mul, hMZ]
    have he : η + star η = 2 * a := by
      simp only [Complex.star_def, Complex.add_conj, a, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [← he, add_smul]
    abel
  have hZcalc : Z = (Complex.I / 2) • (C * Mᴴ * X) - (Complex.I * a) • C := by
    have he := congrArg (fun Q : Matrix ι ι ℂ => (Complex.I / 2) • Q) hXcalc
    simp only [smul_sub, smul_smul] at he
    have hi : (Complex.I / 2) * (2 * Complex.I) = -1 := by
      calc
        _ = Complex.I * Complex.I := by ring
        _ = _ := Complex.I_mul_I
    rw [hi, neg_one_smul, sub_neg_eq_add, show (Complex.I / 2) * (2 * a) = Complex.I * a by ring] at he
    calc
      Z = C * (W * Z) := by rw [← Matrix.mul_assoc, hCW, Matrix.one_mul]
      _ = C * ((Complex.I / 2) • (Mᴴ * X) - (Complex.I * a) • (1 : Matrix ι ι ℂ)) := by
        rw [he, add_sub_cancel_left]
      _ = _ := by rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  have hηc : η * c = -(Complex.I * a) := by dsimp [c]; field_simp [hη]; ring
  have hstar : star (η * c) = -(η * c) := by
    rw [hηc]
    simp only [Complex.star_def, map_neg, map_mul, Complex.conj_I, a, Complex.conj_ofReal, neg_mul]
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero ha')) hη
  have hcim : c.im = -(η.re * η⁻¹.re) := by
    rw [show c = -(a * η⁻¹ * Complex.I) by dsimp [c]; rw [div_eq_mul_inv]; ring,
      Complex.neg_im, Complex.mul_I_im, Complex.mul_re]
    simp only [a, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hinv : 0 < η⁻¹.re := by rw [Complex.inv_re]; exact div_pos ha (Complex.normSq_pos.mpr hη)
  have hcim' : 0 < -c.im := by rw [hcim, neg_neg]; exact mul_pos ha hinv
  have hγ : (η * c ^ 2).re ≠ 0 := by
    have he : η * c ^ 2 = -(a ^ 2) * η⁻¹ := calc
      _ = (-(Complex.I * a)) ^ 2 * η⁻¹ := by
        dsimp only [c]
        field_simp [hη]
        ring
      _ = _ := by rw [neg_sq, mul_pow, Complex.I_sq, neg_one_mul]
    rw [he, ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ha.ne')) hinv.ne'
  have hn (r : ι) (hr : (η * N r r).re = 0) :
      (∀ k, N k r = c * C k r) ∧ (∀ k, N r k = c * C r k) := by
    obtain ⟨hXc, hXr⟩ := hXr r hr
    have hcol (k : ι) : Z k r = (η * c) * C k r := by
      have he := congrArg (fun T : Matrix ι ι ℂ => T k r) hZcalc
      simpa only [hηc, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        hXc, mul_zero, Finset.sum_const_zero, zero_sub, neg_mul] using he
    constructor
    · intro k
      apply mul_left_cancel₀ hη
      simpa only [Z, Matrix.smul_apply, smul_eq_mul, mul_assoc] using hcol k
    · intro k
      apply mul_left_cancel₀ hη
      change Z r k = η * (c * C r k)
      have he := hXr k
      change Z r k + star (Z k r) = 0 at he
      have hce : star (C k r) = C r k := congrArg (fun T : Matrix ι ι ℂ => T r k) hC.eq
      rw [hcol, star_mul', hstar, hce, neg_mul] at he
      exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, mul_assoc] using he))
  obtain ⟨hci, hri⟩ := hn i hxi
  obtain ⟨hcj, hrj⟩ := hn j hxj
  have hOff (r k : ι) (hrk : k ≠ r) (hr : ∀ l, N l r = c * C l r) :
      (h k : ℂ) * C k r + (R * C) k r = 0 := by
    have hfact : (M * N) k r = (M * C) k r * c := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [hr l]
      ring
    have he := congrArg (fun T : Matrix ι ι ℂ => T k r) (M.mul_nonsing_inv hMu)
    change (M * N) k r = (1 : Matrix ι ι ℂ) k r at he
    rw [hfact, Matrix.one_apply_ne hrk] at he
    have hmc := (mul_eq_zero.mp he).resolve_right hc
    simp only [M, B, Matrix.add_mul, Matrix.smul_mul, hWC, Matrix.add_apply, Matrix.diagonal_mul,
      H, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hrk, mul_zero, add_zero] at hmc
    simpa only [add_assoc] using hmc
  have hCij : C i j = 0 := by
    have h₁ := hOff j i hij hcj
    have h₂ := congrArg star (hOff i j hij.symm hci)
    have hC' : star (C j i) = C i j := congrArg (fun T : Matrix ι ι ℂ => T i j) hC.eq
    have hRC' : star ((R * C) j i) = (R * C) i j :=
      congrArg (fun T : Matrix ι ι ℂ => T i j) hRC.eq
    rw [star_add, star_mul', show star (h j : ℂ) = (h j : ℂ) by simp,
      hC', hRC', star_zero] at h₂
    have he : ((h i : ℂ) - h j) * C i j = 0 := by linear_combination h₁ - h₂
    exact (mul_eq_zero.mp he).resolve_left
      (sub_ne_zero.mpr fun he => hij (hh (Complex.ofReal_injective he)))
  have hCji : C j i = 0 := by
    have he := congrArg (fun T : Matrix ι ι ℂ => T j i) hC.eq
    simpa only [Matrix.conjTranspose_apply, hCij, star_zero] using he.symm
  have hCi : C i i ≠ 0 := fun hz =>
    hermitian_orbit_inverse_pair_nonflat h B C θ c hh hC hCu hij hz hCij hCji hm hmax
      hstar hγ hci hcj hri hrj
  have hCj : C j j ≠ 0 := fun hz =>
    hermitian_orbit_inverse_pair_nonflat h B C θ c hh hC hCu hij.symm hz hCji hCij hm hmax
      hstar hγ hcj hci hrj hri
  have hCre (k : ι) : ((C k k).re : ℂ) = C k k := by
    have he := congrArg (fun T : Matrix ι ι ℂ => (T k k).im) hC.eq
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at he
    exact Complex.ext rfl (by simp only [Complex.ofReal_im]; linarith only [he])
  have hb := hermitian_support_maximum_swap_minor_nonpos h B θ hh hmax' ha i j hij
    (by
      change η.re * ((η * N i i).re - (η * N j j).re) =
        (h j - h i) * (η * N i i).re * (η * N j j).re
      simp [hxi, hxj])
  let P := N.submatrix (![i, j] : Fin 2 → ι) (![i, j] : Fin 2 → ι)
  change ((Complex.I / 2) • (P - Pᴴ)).det.re ≤ 0 at hb
  have hP₀ : P 0 0 = c * ((C i i).re : ℂ) := by rw [hCre]; exact hci i
  have hP₁ : P 1 1 = c * ((C j j).re : ℂ) := by rw [hCre]; exact hcj j
  have hP₀₁ : P 0 1 = 0 := by change N i j = _; rw [hcj, hCij, mul_zero]
  have hP₁₀ : P 1 0 = 0 := by change N j i = _; rw [hci, hCji, mul_zero]
  have hscal (x : ℝ) :
      (Complex.I / 2) * (c * (x : ℂ) - star (c * (x : ℂ))) = ((-c.im * x : ℝ) : ℂ) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← sub_mul, ← mul_assoc]
    have h0 : (Complex.I / 2).re = 0 := by norm_num [Complex.div_re]
    have h1 : (Complex.I / 2).im = 1 / 2 := by norm_num [Complex.div_im]
    apply Complex.ext <;>
      simp only [h0, h1, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im] <;> ring
  have hprod : (-c.im) ^ 2 * ((C i i).re * (C j j).re) ≤ 0 := by
    simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.conjTranspose_apply, hP₀, hP₁, hP₀₁, hP₁₀, hscal, star_zero, sub_self,
      mul_zero, sub_zero, ← Complex.ofReal_mul, Complex.ofReal_re] at hb
    convert hb using 1 <;> ring
  have hnonpos := nonpos_of_mul_nonpos_right hprod (pow_pos hcim' 2)
  exact lt_of_le_of_ne hnonpos (mul_ne_zero
    (fun he => hCi ((hCre i).symm.trans (by simp [he])))
    (fun he => hCj ((hCre j).symm.trans (by simp [he]))))

/-- At such a maximum the scaled inverse cannot have three zero diagonal
entries in its Hermitian part. -/
theorem hermitian_orbit_no_three_zero_inverse_diagonal (h : ι → ℝ) (R W : Matrix ι ι ℂ)
    (θ : ℂ) (hh : Function.Injective h) (hR : R.IsHermitian) (hW : W.IsHermitian)
    (hRW : Commute R W) (hWu : IsUnit W.det) {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    let H := diagonal fun r => (h r : ℂ)
    let B := R + Complex.I • W
    let M := H + B
    let η := θ * M.det
    0 < η.re →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (V * H * Vᴴ + B).det).re ≤ η.re) →
    (η * M⁻¹ i i).re = 0 → (η * M⁻¹ j j).re = 0 → (η * M⁻¹ k k).re = 0 → False := by
  intro H B M η ha hmax hi hj hk
  have h₁ := hermitian_orbit_zero_inverse_diagonal_pair h R W θ hh hR hW hRW hWu hij ha hmax hi hj
  have h₂ := hermitian_orbit_zero_inverse_diagonal_pair h R W θ hh hR hW hRW hWu hjk ha hmax hj hk
  have h₃ := hermitian_orbit_zero_inverse_diagonal_pair h R W θ hh hR hW hRW hWu hik ha hmax hi hk
  let x := (W⁻¹ i i).re
  let y := (W⁻¹ j j).re
  let z := (W⁻¹ k k).re
  have he : 0 ≤ (x * y) * (y * z) * (x * z) := by
    rw [show (x * y) * (y * z) * (x * z) = (x * y * z) ^ 2 by ring]
    exact sq_nonneg _
  exact (not_lt_of_ge he) (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h₁ h₂) h₃)

end

end MOC
