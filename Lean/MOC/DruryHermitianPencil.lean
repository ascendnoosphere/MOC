import MOC.Collinear
import MOC.CommonCommutant
import MOC.DruryDistinctReal
import MOC.DruryRepeatedReal
import MOC.SpectralPerturbation
import MOC.StrongSupport
import Mathlib.Topology.Algebra.Polynomial

/-! Drury's three resolvent cases imply the determinant hull inclusion for
real spectra with a nonreal relative scale. -/

open BigOperators Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

private theorem scalar_sub_diagonal_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (x : ℂ) :
    (x • (1 : Matrix ι ι ℂ) - diagonal a).det = ∏ i, (x - a i) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal] <;> rfl

private theorem real_coefficients_of_drury (κ ω : ℂ) (ell : ℝ) :
    star (ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ)) =
      ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ) ∧
    star ((ell : ℂ) - ω - star ω) = (ell : ℂ) - ω - star ω := by
  have hr : star (ell : ℂ) = (ell : ℂ) := by simp [Complex.star_def]
  constructor <;> simp only [star_sub, star_add, star_mul', star_star, hr] <;> ring

private theorem drury_quadratic_has_real_factorization {n : ℕ} [Nonempty (Fin n)]
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAi : IsUnit A.det) (hCi : IsUnit C.det) (κ ξ : ℂ) (hκ : κ ≠ 0)
    (hT : IsUnit (A - κ • C).det)
    (hpenalty : ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      let d := (A - κ • (V * C * Vᴴ)).det - (A - κ • C).det
      (ξ * d).re ≤ -Complex.normSq d / 2)
    (ell : ℝ) (hell : ell ≠ 0)
    (hquad :
      let X := C * A⁻¹
      let ω := ξ * (A - κ • C).det
      (ell : ℂ) • (X * X) + (ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ)) • X +
        ((ell : ℂ) - ω - star ω) • (1 : Matrix (Fin n) (Fin n) ℂ) = 0) :
    ∃ r s : ℝ, r ≠ 0 ∧ s ≠ 0 ∧
      (C * A⁻¹ - (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
        (C * A⁻¹ - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  let X := C * A⁻¹
  let ω := ξ * (A - κ • C).det
  let a := ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ)
  let b := (ell : ℂ) - ω - star ω
  let p : ℝ := a.re / ell
  let q : ℝ := b.re / ell
  change (ell : ℂ) • (X * X) + a • X + b • (1 : Matrix (Fin n) (Fin n) ℂ) = 0 at hquad
  obtain ⟨har, hbr⟩ := real_coefficients_of_drury κ ω ell
  have ha : (a.re : ℂ) = a := Complex.conj_eq_iff_re.mp har
  have hb : (b.re : ℂ) = b := Complex.conj_eq_iff_re.mp hbr
  have hp : (ell : ℂ)⁻¹ * a = (p : ℂ) := by
    dsimp only [p]
    rw [Complex.ofReal_div, ha, div_eq_mul_inv, mul_comm]
  have hq : (ell : ℂ)⁻¹ * b = (q : ℂ) := by
    dsimp only [q]
    rw [Complex.ofReal_div, hb, div_eq_mul_inv, mul_comm]
  have hmonic : X * X + (p : ℂ) • X + (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (ell : ℂ)⁻¹ • M) hquad
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hell),
      one_smul, hp, hq, smul_zero] using h
  have hXdet : IsUnit X.det := by
    change IsUnit (C * A⁻¹).det
    have hAinv : A⁻¹.det ≠ 0 := by
      intro hz
      have h := A.det_nonsing_inv_mul_det hAi
      rw [hz, zero_mul] at h
      exact zero_ne_one h
    rw [Matrix.det_mul]
    exact hCi.mul (isUnit_iff_ne_zero.mpr hAinv)
  have hdegree : X.charpoly.degree ≠ 0 := by
    rw [Matrix.charpoly_degree_eq_dim]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin n) ≠ 0)
  obtain ⟨ρ, hρroot⟩ := IsAlgClosed.exists_root X.charpoly hdegree
  have hdet : (ρ • (1 : Matrix (Fin n) (Fin n) ℂ) - X).det = 0 := by
    have h : X.charpoly.eval ρ = 0 := hρroot
    rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using h
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heig : X *ᵥ v = ρ • v := by
    exact (sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec] using hz)).symm
  have hρpencil : (C - ρ • A).det = 0 := by
    have hfac : C - ρ • A = -(ρ • (1 : Matrix (Fin n) (Fin n) ℂ) - X) * A := by
      simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, neg_sub,
        X, Matrix.mul_assoc, A.nonsing_inv_mul hAi, Matrix.mul_one]
    rw [hfac, Matrix.det_mul, Matrix.det_neg, hdet, mul_zero, zero_mul]
  have hρreal : star ρ = ρ := by
    by_contra hn
    exact det_pencil_ne_zero_of_quadratic_support A C hA hC κ ξ ρ hκ (Ne.symm hn)
      hT hpenalty hρpencil
  let r : ℝ := ρ.re
  have hr : (r : ℂ) = ρ := Complex.conj_eq_iff_re.mp hρreal
  have hr₀ : r ≠ 0 := by
    intro hz
    have hzero : ρ = 0 := hr.symm.trans (by simp [hz])
    have h := hdet
    simp only [hzero, zero_smul, zero_sub, Matrix.det_neg] at h
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (isUnit_iff_ne_zero.mp hXdet)) h
  have hpoly : ρ * ρ + (p : ℂ) * ρ + (q : ℂ) = 0 := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v) hmonic
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, ← Matrix.mulVec_mulVec,
      heig, Matrix.mulVec_smul, smul_smul, Matrix.one_mulVec, Matrix.zero_mulVec,
      ← add_smul] at he
    exact (smul_eq_zero.mp he).resolve_right hv
  let s : ℝ := -p - r
  have hsum : (r : ℂ) + (s : ℂ) = -(p : ℂ) := by
    simp only [s, Complex.ofReal_sub, Complex.ofReal_neg]
    abel
  have hprod : (r : ℂ) * (s : ℂ) = (q : ℂ) := by
    simp only [s, Complex.ofReal_sub, Complex.ofReal_neg, hr]
    linear_combination -hpoly
  let R := X - (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  let S := X - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hsplit : R * S = 0 := by
    calc
      _ = X * X - ((r : ℂ) + (s : ℂ)) • X +
          ((r : ℂ) * (s : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [R, S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul, smul_sub, smul_smul, add_smul,
          mul_comm (s : ℂ) (r : ℂ)]
        abel
      _ = 0 := by simpa only [hsum, hprod, neg_smul, sub_neg_eq_add] using hmonic
  by_cases hs : s = 0
  · have hRX : R * X = 0 := by simpa only [S, hs, Complex.ofReal_zero, zero_smul, sub_zero] using hsplit
    have hR : R = 0 := by
      calc
        R = R * (X * X⁻¹) := by rw [X.mul_nonsing_inv hXdet, Matrix.mul_one]
        _ = 0 := by rw [← Matrix.mul_assoc, hRX, Matrix.zero_mul]
    exact ⟨r, r, hr₀, hr₀, by change R * R = 0; rw [hR, Matrix.zero_mul]⟩
  · exact ⟨r, s, hr₀, hs, hsplit⟩

private theorem eventually_polynomial_eval_ne_zero (p : Polynomial ℝ) (h : p.eval 1 ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), p.eval t ≠ 0 := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact h eval_zero
  have hroots : IsClosed ({t : ℝ | p.IsRoot t} \ {0}) :=
    ((finite_setOf_isRoot hp).subset Set.diff_subset).isClosed
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∉ ({s : ℝ | p.IsRoot s} \ {0}) :=
    hroots.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht h₀
  exact fun hz => ht ⟨hz, h₀⟩

private theorem exists_regular_hermitian_spectra_of_support_violation {n : ℕ}
    (a c : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (μ η : ℂ)
    (h : ∀ σ : Equiv.Perm (Fin n),
      (η * matchingProduct (fun i => (a i : ℂ)) (fun i => μ * (c i : ℂ)) σ).re <
        (η * determinantValue (fun i => (a i : ℂ)) (fun i => μ * (c i : ℂ)) U).re) :
    ∃ a' c' : Fin n → ℝ, (∀ i, a' i ≠ 0) ∧ (∀ i, c' i ≠ 0) ∧
      Function.Injective a' ∧ Function.Injective c' ∧
      Function.Injective (fun p : Fin n × Fin n => (c' p.1 : ℂ) / (a' p.2 : ℂ)) ∧
      ∀ σ : Equiv.Perm (Fin n),
        (η * matchingProduct (fun i => (a' i : ℂ)) (fun i => μ * (c' i : ℂ)) σ).re <
          (η * determinantValue (fun i => (a' i : ℂ)) (fun i => μ * (c' i : ℂ)) U).re := by
  let a₁ (i : Fin n) : ℝ := (2 : ℝ) ^ i.val
  let c₁ (i : Fin n) : ℝ := (2 : ℝ) ^ (n * i.val)
  have hcross₁ (p q : Fin n × Fin n) (hpq : p ≠ q) :
      c₁ p.1 * a₁ q.2 - c₁ q.1 * a₁ p.2 ≠ 0 := by
    intro he
    have hexp : n * p.1.val + q.2.val = n * q.1.val + p.2.val :=
      (pow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective
        (by simpa only [a₁, c₁, ← pow_add] using sub_eq_zero.mp he)
    have hpair : (p.1, q.2) = (q.1, p.2) := by
      apply (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n)).injective
      apply Fin.ext
      change q.2.val + n * p.1.val = p.2.val + n * q.1.val
      simpa only [Nat.add_comm] using hexp
    obtain ⟨hfst, hsnd⟩ := Prod.mk.inj hpair
    exact hpq (Prod.ext hfst hsnd.symm)
  let L (x y : ℝ) : Polynomial ℝ := C x + X * C (y - x)
  have hL₀ (x y : ℝ) : (L x y).eval 0 = x := by simp [L]
  have hL₁ (x y : ℝ) : (L x y).eval 1 = y := by simp [L] <;> ring
  let P (i : Fin n) := L (a i) (a₁ i)
  let Q (i : Fin n) := L (c i) (c₁ i)
  let ar (t : ℝ) (i : Fin n) := (P i).eval t
  let cr (t : ℝ) (i : Fin n) := (Q i).eval t
  have hnz : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i, ar t i ≠ 0 ∧ cr t i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    have hP : (P i).eval 1 ≠ 0 := by
      simpa only [P, hL₁, a₁] using pow_ne_zero i.val (by norm_num : (2 : ℝ) ≠ 0)
    have hQ : (Q i).eval 1 ≠ 0 := by
      simpa only [Q, hL₁, c₁] using pow_ne_zero (n * i.val) (by norm_num : (2 : ℝ) ≠ 0)
    exact (eventually_polynomial_eval_ne_zero (P i) hP).and
      (eventually_polynomial_eval_ne_zero (Q i) hQ)
  have hcross : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ p q : Fin n × Fin n, p ≠ q →
      cr t p.1 * ar t q.2 ≠ cr t q.1 * ar t p.2 := by
    apply Filter.eventually_all.mpr
    intro p
    apply Filter.eventually_all.mpr
    intro q
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ hne => (hne hpq).elim
    let R := Q p.1 * P q.2 - Q q.1 * P p.2
    have hR : R.eval 1 ≠ 0 := by
      simpa only [R, P, Q, eval_sub, eval_mul, hL₁] using hcross₁ p q hpq
    filter_upwards [eventually_polynomial_eval_ne_zero R hR] with t ht _
    simpa only [R, ar, cr, eval_sub, eval_mul, sub_ne_zero] using ht
  let ac (t : ℝ) (i : Fin n) : ℂ := ar t i
  let bc (t : ℝ) (i : Fin n) : ℂ := μ * (cr t i : ℂ)
  have hac₀ : ac 0 = fun i => (a i : ℂ) := by
    funext i
    simp only [ac, ar, P, hL₀]
  have hbc₀ : bc 0 = fun i => μ * (c i : ℂ) := by
    funext i
    simp only [bc, cr, Q, hL₀]
  have hca : Continuous ac := continuous_pi fun i =>
    Complex.continuous_ofReal.comp (P i).continuous
  have hcb : Continuous bc := continuous_pi fun i =>
    continuous_const.mul (Complex.continuous_ofReal.comp (Q i).continuous)
  have hd : Continuous (fun t => (η * determinantValue (ac t) (bc t) U).re) := by
    unfold determinantValue
    fun_prop
  have hm (σ : Equiv.Perm (Fin n)) :
      Continuous (fun t => (η * matchingProduct (ac t) (bc t) σ).re) := by
    have hp : Continuous (fun t => matchingProduct (ac t) (bc t) σ) := by
      unfold matchingProduct
      apply continuous_finset_prod
      intro i _
      fun_prop
    fun_prop
  have hstrict : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm (Fin n),
      (η * matchingProduct (ac t) (bc t) σ).re < (η * determinantValue (ac t) (bc t) U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    exact ((hm σ).continuousAt.eventually_lt hd.continuousAt
      (by simpa only [hac₀, hbc₀] using h σ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htnz, htcross, htstrict⟩ := (hnz.and (hcross.and hstrict)).exists
  have hratios : Function.Injective (fun p : Fin n × Fin n => (cr t p.1 : ℂ) / (ar t p.2 : ℂ)) := by
    classical
    intro p q he
    by_contra hpq
    have hmul := (div_eq_div_iff (Complex.ofReal_ne_zero.mpr (htnz p.2).1)
      (Complex.ofReal_ne_zero.mpr (htnz q.2).1)).mp he
    apply htcross p q hpq
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul] using hmul
  refine ⟨ar t, cr t, fun i => (htnz i).1, fun i => (htnz i).2, ?_, ?_, hratios, htstrict⟩
  · intro i j he
    have hp : (i, i) = (i, j) := hratios (by
      change (cr t i : ℂ) / (ar t i : ℂ) = (cr t i : ℂ) / (ar t j : ℂ)
      rw [he])
    exact congrArg Prod.snd hp
  · intro i j he
    have hp : (i, i) = (j, i) := hratios (by
      change (cr t i : ℂ) / (ar t i : ℂ) = (cr t j : ℂ) / (ar t i : ℂ)
      rw [he])
    exact congrArg Prod.fst hp

/-- The Marcus–de Oliveira inclusion for two real spectral lists when one
list is multiplied by a nonreal unit scalar. -/
theorem holds_hermitian_pencil (κ : ℂ) (hκ : κ * star κ = 1) (hκi : κ.im ≠ 0)
    {n : ℕ} (a c : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => -κ * (c i : ℂ)) U := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 3
    · exact conjecture_le_three hn _ _ U hU
    have hn₄ : 4 ≤ n := by omega
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    by_contra hnot
    rw [holds_iff_directional] at hnot
    push_neg at hnot
    obtain ⟨η, hsep⟩ := hnot
    obtain ⟨a', c', ha₀, hc₀, haInj, hcInj, hRatios, hsep'⟩ :=
      exists_regular_hermitian_spectra_of_support_violation a c U (-κ) η hsep
    let ap (i : Fin n) : ℂ := a' i
    let cp (i : Fin n) : ℂ := c' i
    let bp (i : Fin n) : ℂ := -κ * cp i
    obtain ⟨V, ξ, hV, hstrict, hpen, _⟩ :=
      exists_quadratic_support_frobenius_maximizer ap bp U hU η hsep'
    have hfail : ¬ Holds ap bp V := by
      intro hh
      obtain ⟨σ, hσ⟩ := (holds_iff_directional ap bp V).mp hh ξ
      exact (not_le_of_gt (hstrict σ)) hσ
    have hnoBlocks : ¬ HasProperPairedBlocks V := by
      rintro ⟨m, k, er, ec, P, Q, hm, hk, hblock⟩
      have hcard := Fintype.card_congr er
      simp only [Fintype.card_sum, Fintype.card_fin] at hcard
      have hPQ : IsUnitary (fromBlocks P 0 0 Q) := hblock ▸ unitary_reindex er ec hV
      obtain ⟨hP, hQ⟩ := unitary_directSum_iff.mp hPQ
      have h₁ := ih m (by omega) (fun i => a' (er (.inl i))) (fun i => c' (ec (.inl i))) P hP
      have h₂ := ih k (by omega) (fun i => a' (er (.inr i))) (fun i => c' (ec (.inr i))) Q hQ
      apply hfail
      apply (holds_reindex_iff er ec ap bp V).mp
      rw [hblock]
      have ha : ap ∘ er = Sum.elim (fun i => ap (er (.inl i))) (fun i => ap (er (.inr i))) := by
        funext i
        cases i <;> rfl
      have hb : bp ∘ ec = Sum.elim (fun i => bp (ec (.inl i))) (fun i => bp (ec (.inr i))) := by
        funext i
        cases i <;> rfl
      rw [ha, hb]
      exact holds_directSum _ _ _ _ P Q h₁ h₂
    have hκ₀ : κ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hκ
      exact zero_ne_one hκ
    have hκ' : κ ≠ star κ := by
      intro hh
      exact hκi (Complex.conj_eq_iff_im.mp hh.symm)
    have hξ : ξ ≠ 0 := by
      intro he
      simpa [he] using hstrict (Equiv.refl (Fin n))
    let A := diagonal ap
    let C := V * diagonal cp * Vᴴ
    let T := A - κ • C
    have hAre : A.IsHermitian := by
      apply Matrix.isHermitian_diagonal_iff.mpr
      simp [ap, isSelfAdjoint_iff, Complex.star_def]
    have hCre : (diagonal cp).IsHermitian := by
      apply Matrix.isHermitian_diagonal_iff.mpr
      simp [cp, isSelfAdjoint_iff, Complex.star_def]
    have hCH : C.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hCre
    have haNZ (i : Fin n) : ap i ≠ 0 := Complex.ofReal_ne_zero.mpr (ha₀ i)
    have hcNZ (i : Fin n) : cp i ≠ 0 := Complex.ofReal_ne_zero.mpr (hc₀ i)
    have hAi : IsUnit A.det := by
      rw [show A = diagonal ap from rfl, Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => haNZ i)
    have hCi : IsUnit C.det := by
      rw [show C = V * diagonal cp * Vᴴ from rfl, det_unitary_conjugation _ _ hV,
        Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hcNZ i)
    have hvalue (R : Matrix (Fin n) (Fin n) ℂ) :
        determinantValue ap bp (R * V) = (A - κ • (R * C * Rᴴ)).det := by
      change (A + (R * V) * diagonal ((-κ) • cp) * (R * V)ᴴ).det = _
      rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, sub_eq_add_neg, C]
    have he : determinantValue ap bp V = T.det := by
      simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, T] using
        hvalue (1 : Matrix (Fin n) (Fin n) ℂ)
    have hT : IsUnit T.det := by
      rw [← he, isUnit_iff_ne_zero]
      exact fun hz => hfail (holds_of_singular ap bp hV hz)
    have hpenalty (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnitary R) :
        let d := (A - κ • (R * C * Rᴴ)).det - T.det
        (ξ * d).re ≤ -Complex.normSq d / 2 := by
      have hR' : IsUnitary Rᴴ := ⟨by simpa using hR.2, by simpa using hR.1⟩
      have hRV : IsUnitary (R * V) := by
        simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ V hR' hV
      simpa only [hvalue, he] using hpen (R * V) hRV
    obtain ⟨ell, hell, hquad⟩ := exists_drury_quadratic_of_simple_support_maximum
      (by omega) (Complex.ofReal_injective.comp haInj) (Complex.ofReal_injective.comp hcInj)
      hV (card_lt_supportColumns_of_no_paired_blocks hV hnoBlocks)
      κ ξ hκ hκ' hξ hAre hCre hAi hT hpenalty
    obtain ⟨r, s, hr₀, hs₀, hsplit⟩ :=
      drury_quadratic_has_real_factorization A C hAre hCH hAi hCi κ ξ hκ₀ hT hpenalty ell hell hquad
    have hden (u : ℝ) : 1 - κ * (u : ℂ) ≠ 0 := by
      intro hz
      have him := congrArg Complex.im (sub_eq_zero.mp hz)
      simp only [Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add] at him
      have hu : u = 0 := (mul_eq_zero.mp him.symm).resolve_left hκi
      simp [hu] at hz
    have hbase (x : ℂ) (hx : (x • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = 0) :
        ∃ j, x = ap j := by
      change (x • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal ap).det = 0 at hx
      rw [scalar_sub_diagonal_det] at hx
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hx
      exact ⟨j, sub_eq_zero.mp hj⟩
    have hother (i : Fin n) : (cp i • (1 : Matrix (Fin n) (Fin n) ℂ) - C).det = 0 := by
      have hconj : cp i • (1 : Matrix (Fin n) (Fin n) ℂ) - C =
          V * (cp i • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal cp) * Vᴴ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hV.1, C]
      rw [hconj, det_unitary_conjugation _ _ hV, scalar_sub_diagonal_det]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    by_cases hrs : r = s
    · subst s
      exact no_generic_quadratic_support_of_repeated_real_drury (by omega) A C hAre hCH hAi
        r hr₀ κ ξ hκ₀ (hden r) ap cp haNZ hbase hother hRatios hsplit hT hpenalty
    · exact no_generic_quadratic_support_of_split_real_drury (by omega) A C hAre hCH hAi
        r s hrs hr₀ hs₀ κ ξ hκ₀ (hden r) (hden s) ap cp haNZ hbase hother hRatios hsplit hT hpenalty

/-- The determinant hull inclusion for two spectra on affine lines, with
independent directions and offsets. -/
theorem holds_of_affine_spectral_lines {n : ℕ} (a c : Fin n → ℝ) (p q s t : ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun i => p * (a i : ℂ) + s) (fun i => q * (c i : ℂ) + t) U := by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, zero_add]
    apply (holds_swap_iff _ _ hU).mp
    have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    exact holds_of_commute _ _ hU' (Matrix.scalar_commute s (Commute.all s) Uᴴ).symm
  let z := q / p
  have hpz : p * z = q := by
    dsimp only [z]
    rw [mul_comm, div_mul_cancel₀ _ hp]
  by_cases hz : z.im = 0
  · have hzr : (z.re : ℂ) = z := Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr hz)
    simpa only [Complex.ofReal_mul, hzr, ← mul_assoc, hpz] using
      holds_of_parallel_affine_lines a (fun i => z.re * c i) p s t U hU
  let w := (s + t) / p
  let v : ℝ := w.im / z.im
  let u : ℝ := w.re - z.re * v
  have hpw : p * w = s + t := by
    dsimp only [w]
    rw [mul_comm, div_mul_cancel₀ _ hp]
  have hcoord : (u : ℂ) + z * (v : ℂ) = w := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, u]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add, v]
      rw [mul_comm, div_mul_cancel₀ _ hz]
  let r : ℝ := ‖z‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr (fun he => hz (by simp [he]))
  let κ := -(z / (r : ℂ))
  have hNorm : Complex.normSq κ = 1 := by
    simp only [κ, Complex.normSq_neg, Complex.normSq_div, Complex.normSq_ofReal,
      ← pow_two, Complex.sq_norm, r]
    exact div_self (Complex.normSq_pos.mpr (norm_ne_zero_iff.mp hr)).ne'
  have hκ : κ * star κ = 1 := by rw [Complex.star_def, Complex.mul_conj, hNorm, Complex.ofReal_one]
  have hκi : κ.im ≠ 0 := by
    simpa only [κ, Complex.neg_im, Complex.div_ofReal_im, neg_ne_zero] using div_ne_zero hz hr
  let A (i : Fin n) : ℂ := ((a i + u : ℝ) : ℂ)
  let B (i : Fin n) : ℂ := z * ((c i + v : ℝ) : ℂ)
  have hB : (fun i => -κ * ((r * (c i + v) : ℝ) : ℂ)) = B := by
    funext i
    simp only [κ, neg_neg, Complex.ofReal_mul, ← mul_assoc,
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr), B]
  have hbase : Holds A B U := by
    simpa only [A, hB] using
      holds_hermitian_pencil κ hκ hκi (fun i => a i + u) (fun i => r * (c i + v)) U hU
  have hscaled : Holds (fun i => p * A i) (fun i => p * B i) U :=
    hull_of_common_factor (determinantValue_scale A B U p) (matchingProduct_scale A B p) hbase
  have hshift := (holds_shift_iff (fun i => p * A i) (fun i => p * B i) hU
    (s - p * (u : ℂ))).mpr hscaled
  have ha (i : Fin n) : p * A i + (s - p * (u : ℂ)) = p * (a i : ℂ) + s := by
    simp only [A, Complex.ofReal_add]
    ring
  have hb (i : Fin n) : p * B i - (s - p * (u : ℂ)) = q * (c i : ℂ) + t := by
    calc
      _ = (p * z) * (c i : ℂ) + p * ((u : ℂ) + z * (v : ℂ)) - s := by
        simp only [B, Complex.ofReal_add]
        ring
      _ = _ := by rw [hpz, hcoord, hpw]; ring
  simpa only [ha, hb] using hshift

end

end MOC
