import MOC.RankOneDefectCompression
import MOC.Reformulations.QuadraticDiskCertificate
import MOC.Small
import Mathlib.Tactic.LinearCombination

/-! Exact induction criteria for a rank-one defective compression.
The support threshold uses all injections into the extra partner list. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem rankOnePhase_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (x y : ℂ) :
    rankOnePhase v x * rankOnePhase v y = rankOnePhase v (x * y) := by
  let P := vecMulVec v (star ∘ v)
  have hP : P * P = P := by
    ext i j : 1
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Function.comp_apply]
    calc
      _ = ∑ k, (v i * star (v j)) * (star (v k) * v k) :=
        Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [← Finset.mul_sum, hv, mul_one]
  change (1 + (x - 1) • P) * (1 + (y - 1) • P) = 1 + (x * y - 1) • P
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP]
  ext i j : 1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A rank-one phase in the unit disk gives a positive Gram defect of
rank at most one, even after a fixed unitary on its right. -/
theorem rankOnePhase_mul_gramDefect (v : Fin n → ℂ) (z : ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnitary W)
    (hv : ∑ i, star (v i) * v i = 1) (hz : ‖z‖ ≤ 1) :
    let V := rankOnePhase v z * W
    (1 - Vᴴ * V).PosSemidef ∧ (1 - Vᴴ * V).rank ≤ 1 := by
  let D := rankOnePhase v z
  let V := D * W
  have hV : V * Vᴴ = D * Dᴴ := by
    rw [V, Matrix.conjTranspose_mul, Matrix.mul_assoc D W (Wᴴ * Dᴴ),
      ← Matrix.mul_assoc W Wᴴ Dᴴ, hW.1, Matrix.one_mul]
  have hD : D * Dᴴ = rankOnePhase v ((Complex.normSq z : ℝ) : ℂ) := by
    rw [D, rankOnePhase_conjTranspose, rankOnePhase_mul v hv,
      Complex.star_def, Complex.mul_conj]
  have hδ : 0 ≤ 1 - Complex.normSq z := by
    rw [sub_nonneg, Complex.normSq_eq_norm_sq]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
  let t : ℂ := (Real.sqrt (1 - Complex.normSq z) : ℝ)
  have ht : t * star t = (((1 : ℝ) - Complex.normSq z : ℝ) : ℂ) := by
    rw [show star t = t from Complex.conj_ofReal _, ← pow_two, t, ← Complex.ofReal_pow,
      Real.sq_sqrt hδ]
  let C : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun i _ => t * v i
  have hdef : 1 - V * Vᴴ = C * Cᴴ := by
    rw [hV, hD, rankOnePhase]
    ext i j : 1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Function.comp_apply, Matrix.mul_apply, Fin.sum_univ_one,
      Matrix.conjTranspose_apply, C, Matrix.of_apply, star_mul']
    rw [show t * v i * (star (v j) * star t) =
      (t * star t) * (v i * star (v j)) by ring, ht, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  apply (rank_one_defect_left_iff_right V).mpr
  rw [hdef]
  exact ⟨Matrix.posSemidef_self_mul_conjTranspose C,
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width C)⟩

/-- The largest projected injection product with one extra zero partner. -/
def rankOneDefectInjectionSupport (a b : Fin n → ℂ) (η : ℂ) : ℝ :=
  Finset.univ.sup' ⟨Fin.succEmb n, Finset.mem_univ _⟩
    (fun e => (η * rectangularMatchingProduct a (Fin.cons 0 b) e).re)

private theorem le_rankOneDefectInjectionSupport (a b : Fin n → ℂ) (η : ℂ)
    (e : Fin n ↪ Fin (n + 1)) :
    (η * rectangularMatchingProduct a (Fin.cons 0 b) e).re ≤
      rankOneDefectInjectionSupport a b η :=
  Finset.le_sup' _ (Finset.mem_univ e)

private theorem rankOneDefect_hull_iff (a b : Fin n → ℂ) (w : ℂ) :
    w ∈ convexHull ℝ (Set.range (rectangularMatchingProduct a (Fin.cons 0 b))) ↔
      ∀ η : ℂ, (η * w).re ≤ rankOneDefectInjectionSupport a b η := by
  classical
  constructor
  · intro hw η
    let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
    change L w ≤ _
    apply convexHull_min ?_ (convex_halfSpace_le L.isLinear _) hw
    rintro _ ⟨e, rfl⟩
    exact le_rankOneDefectInjectionSupport a b η e
  · intro hw
    apply mem_hull_of_directional_bound
    intro η
    obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin n ↪ Fin (n + 1))))
      ⟨Fin.succEmb n, Finset.mem_univ _⟩
      (fun e => (η * rectangularMatchingProduct a (Fin.cons 0 b) e).re)
    exact ⟨e, (hw η).trans_eq (by simpa only [rankOneDefectInjectionSupport] using he)⟩

private theorem squareMatching_le_rankOneDefectInjectionSupport (a b : Fin n → ℂ) (η : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    (η * matchingProduct a b σ).re ≤ rankOneDefectInjectionSupport a b η := by
  let e := σ.symm.toEmbedding.trans (Fin.succEmb n)
  have he : matchingProduct a b σ = rectangularMatchingProduct a (Fin.cons 0 b) e := by
    simpa only [rectangularMatchingProduct, e, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Fin.coe_succEmb, Fin.cons_succ, Equiv.symm_symm] using (matchingProduct_inverse a b σ.symm)
  simpa only [← he] using le_rankOneDefectInjectionSupport a b η e

/-- The three coefficients of the projected rank-one phase determinant. -/
structure RankOneDefectDiskCoefficients where
  constant : ℝ
  radial : ℝ
  linear : ℂ

/-- Read the constant, radial, and linear coefficients from five phase values. -/
def rankOneDefectDiskCoefficients (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ)
    (η : ℂ) : RankOneDefectDiskCoefficients :=
  let F (z : ℂ) := (η * determinantValue a b (rankOnePhase v z * W)).re
  ⟨F 0, (F 1 + F (-1)) / 2 - F 0,
    ⟨(F 1 - F (-1)) / 4, (F (-Complex.I) - F Complex.I) / 4⟩⟩

private theorem rankOneDefectDisk_eval (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ)
    (η z : ℂ) :
    let C := rankOneDefectDiskCoefficients a b v W η
    (η * determinantValue a b (rankOnePhase v z * W)).re =
      C.constant + 2 * (C.linear * z).re + C.radial * ‖z‖ ^ 2 := by
  let F (z : ℂ) := (η * determinantValue a b (rankOnePhase v z * W)).re
  let C := rankOneDefectDiskCoefficients a b v W η
  have hF (u : ℂ) :
      F u = (η * (diagonal a +
        rankOnePhase v u * (W * diagonal b * Wᴴ) * (rankOnePhase v u)ᴴ).det).re := by
    simp only [F, determinantValue, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := rankOneCompressionDisk_support (diagonal a) (W * diagonal b * Wᴴ) v η z
  simp only [← hF] at h
  change F z = C.constant + 2 * (C.linear * z).re + C.radial * ‖z‖ ^ 2
  rw [h, Complex.normSq_eq_norm_sq, Complex.mul_re]
  change _ = F 0 + 2 * (((F 1 - F (-1)) / 4) * z.re -
    ((F (-Complex.I) - F Complex.I) / 4) * z.im) + ((F 1 + F (-1)) / 2 - F 0) * ‖z‖ ^ 2
  ring

/-- The full disk bound for every rank-one phase family. -/
def RankOneDefectDiskBound (n : ℕ) : Prop :=
  ∀ (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsUnitary W →
    (∑ i, star (v i) * v i = 1) → ∀ (η z : ℂ), ‖z‖ ≤ 1 →
      (η * determinantValue a b (rankOnePhase v z * W)).re ≤ rankOneDefectInjectionSupport a b η

/-- The only additional inequality needed in the interior branch. -/
def RankOneDefectAbsorption (n : ℕ) : Prop :=
  ∀ (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsUnitary W →
    (∑ i, star (v i) * v i = 1) → ∀ η : ℂ,
      let C := rankOneDefectDiskCoefficients a b v W η
      C.radial < -‖C.linear‖ →
        ‖C.linear‖ ^ 2 ≤ (-C.radial) * (rankOneDefectInjectionSupport a b η - C.constant)

/-- Order `n+1` implies the rank-one disk bound in order `n`. -/
theorem rankOneDefectDiskBound_of_conjecture (h : Conjecture (Fin (n + 1))) :
    RankOneDefectDiskBound n := by
  intro a b v W hW hv η z hz
  obtain ⟨hp, hr⟩ := rankOnePhase_mul_gramDefect v z W hW hv hz
  exact (rankOneDefect_hull_iff a b _).mp
    ((conjecture_iff_rankOneDefect n).mp h a b (rankOnePhase v z * W) hp hr) η

/-- The full disk bound implies the next order. The phase one
includes every unitary corner. -/
theorem conjecture_succ_of_rankOneDefectDiskBound
    (hDisk : RankOneDefectDiskBound n) : Conjecture (Fin (n + 1)) := by
  cases n with
  | zero => exact conjecture_le_three (by decide)
  | succ n =>
    apply (conjecture_iff_rankOneDefect (n + 1)).mpr
    intro a b V hV hr
    apply (rankOneDefect_hull_iff a b _).mpr
    intro η
    rcases rankOneDefect_unitary_or_rankOnePhase V hV hr with hU | ⟨v, z, W, hv, hz, hW, he⟩
    · let v : Fin (n + 1) → ℂ := Pi.single 0 1
      have hv : ∑ i, star (v i) * v i = 1 := by
        rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 1)) (Finset.mem_univ _)]
        · simp [v]
        · intro i _ hi
          simp [v, Pi.single_apply, hi, Ne.symm hi]
      have h := hDisk a b v V hU hv η 1 (by simp)
      simpa only [rankOnePhase, sub_self, zero_smul, add_zero, Matrix.one_mul] using h
    · rw [he]
      exact hDisk a b v W hW hv η z hz.le

/-- The unrestricted next-order conjecture is equivalent to the full
disk bound in the retained order. -/
theorem conjecture_succ_iff_rankOneDefectDiskBound :
    Conjecture (Fin (n + 1)) ↔ RankOneDefectDiskBound n :=
  ⟨rankOneDefectDiskBound_of_conjecture, conjecture_succ_of_rankOneDefectDiskBound⟩

/-- Eliminate the phase variable using the exact piecewise maximum. -/
theorem rankOneDefectDiskBound_iff_piecewise :
    RankOneDefectDiskBound n ↔
      ∀ (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsUnitary W →
        (∑ i, star (v i) * v i = 1) → ∀ η : ℂ,
        let C := rankOneDefectDiskCoefficients a b v W η
        (if -‖C.linear‖ ≤ C.radial then C.constant + 2 * ‖C.linear‖ + C.radial
          else C.constant + ‖C.linear‖ ^ 2 / (-C.radial)) ≤ rankOneDefectInjectionSupport a b η := by
  constructor
  · intro h a b v W hW hv η
    let C := rankOneDefectDiskCoefficients a b v W η
    obtain ⟨_, z, hz, he, _⟩ := quadraticDiskSupport_max C.constant C.radial C.linear
    have hle := h a b v W hW hv η z hz
    rw [rankOneDefectDisk_eval a b v W η z, he] at hle
    exact hle
  · intro h a b v W hW hv η z hz
    let C := rankOneDefectDiskCoefficients a b v W η
    rw [rankOneDefectDisk_eval a b v W η z]
    exact ((quadraticDiskSupport_max C.constant C.radial C.linear).1 z hz).trans
      (h a b v W hW hv η)

/-- A two-by-two positive-semidefinite certificate for each projected family. -/
def RankOneDefectSemidefinite (n : ℕ) : Prop :=
  ∀ (a b v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsUnitary W →
    (∑ i, star (v i) * v i = 1) → ∀ η : ℂ,
    let C := rankOneDefectDiskCoefficients a b v W η
    ∃ λ : ℝ, 0 ≤ λ ∧ (Reformulations.diskCertificateMatrix
      (rankOneDefectInjectionSupport a b η - C.constant - λ) (λ - C.radial) C.linear).PosSemidef

theorem rankOneDefectDiskBound_iff_semidefinite :
    RankOneDefectDiskBound n ↔ RankOneDefectSemidefinite n := by
  constructor
  · intro h a b v W hW hv η
    apply (Reformulations.quadratic_disk_bound_iff_semidefinite _ _ _ _).mp
    intro z hz
    rw [← rankOneDefectDisk_eval a b v W η z]
    exact h a b v W hW hv η z hz
  · intro h a b v W hW hv η z hz
    rw [rankOneDefectDisk_eval a b v W η z]
    exact (Reformulations.quadratic_disk_bound_iff_semidefinite _ _ _ _).mpr
      (h a b v W hW hv η) z hz

/-- The unrestricted next order is equivalent to the semidefinite
certificate in the retained order. -/
theorem conjecture_succ_iff_rankOneDefectSemidefinite :
    Conjecture (Fin (n + 1)) ↔ RankOneDefectSemidefinite n :=
  conjecture_succ_iff_rankOneDefectDiskBound.trans rankOneDefectDiskBound_iff_semidefinite

/-- In the interior branch a failed absorption inequality gives an
attained disk value strictly above the injection threshold. -/
theorem rankOneDefectDiskBound_implies_absorption (h : RankOneDefectDiskBound n) :
    RankOneDefectAbsorption n := by
  intro a b v W hW hv η
  let C := rankOneDefectDiskCoefficients a b v W η
  change C.radial < -‖C.linear‖ → _
  intro hi
  obtain ⟨_, z, hz, he, _⟩ := quadraticDiskSupport_max C.constant C.radial C.linear
  rw [if_neg (not_le_of_gt hi)] at he
  have hle := h a b v W hW hv η z hz
  rw [rankOneDefectDisk_eval a b v W η z, he] at hle
  have hpos : 0 < -C.radial := by linarith only [hi, norm_nonneg C.linear]
  have hdiv : ‖C.linear‖ ^ 2 / (-C.radial) ≤ rankOneDefectInjectionSupport a b η - C.constant := by
    linarith only [hle]
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

/-- A smaller-order proof covers the boundary branch. Defect absorption
is then exactly the remaining condition for the next order. -/
theorem conjecture_succ_iff_rankOneDefectAbsorption (hSmall : Conjecture (Fin n)) :
    Conjecture (Fin (n + 1)) ↔ RankOneDefectAbsorption n := by
  refine ⟨fun h => rankOneDefectDiskBound_implies_absorption (rankOneDefectDiskBound_of_conjecture h), ?_⟩
  intro h
  apply conjecture_succ_of_rankOneDefectDiskBound
  intro a b v W hW hv η z hz
  have hb := rankOneCompressionDisk_support_le_of_interior hSmall a b v W hW hv η
    (rankOneDefectInjectionSupport a b η) (squareMatching_le_rankOneDefectInjectionSupport a b η)
  have hs (u : ℂ) :
      (η * (diagonal a + rankOnePhase v u * (W * diagonal b * Wᴴ) * (rankOnePhase v u)ᴴ).det).re =
      (η * determinantValue a b (rankOnePhase v u * W)).re := by
    simp only [determinantValue, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simpa only [hs] using (show _ from hb (by
    simpa only [hs, rankOneDefectDiskCoefficients] using h a b v W hW hv η) z hz)

/-- The absorption condition is an unrestricted equivalent in order
four because the order-three inclusion holds. -/
theorem conjecture_four_iff_rankOneDefectAbsorption :
    Conjecture (Fin 4) ↔ RankOneDefectAbsorption 3 :=
  conjecture_succ_iff_rankOneDefectAbsorption (conjecture_le_three le_rfl)

/-- Solving defect absorption in all orders is equivalent to solving
the unrestricted conjecture in every finite order. -/
theorem conjecture_all_iff_rankOneDefectAbsorption :
    (∀ n : ℕ, Conjecture (Fin n)) ↔ ∀ n : ℕ, RankOneDefectAbsorption n := by
  refine ⟨fun h n => (conjecture_succ_iff_rankOneDefectAbsorption (h n)).mp (h (n + 1)), ?_⟩
  intro h n
  induction n with
  | zero => exact conjecture_le_three (by decide)
  | succ n ih => exact (conjecture_succ_iff_rankOneDefectAbsorption ih).mpr (h n)

/-! Prove that the stated interior quadratic inequality holds for all
spectra and phase directions. This would prove the next-order inclusion
from the preceding order. -/

end

end MOC
