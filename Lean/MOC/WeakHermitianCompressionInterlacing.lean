import MOC.HermitianCompressionInterlacing
import MOC.FullSupportReduction
import MOC.Variational

open Matrix

namespace MOC

noncomputable section

/-- The eigenvalues of every Hermitian principal compression weakly
interlace the ordered eigenvalues of the original matrix. -/
theorem exists_interlacing_of_hermitian_compression {n : ℕ}
    (lam : Fin (n + 1) → ℝ) (hlam : Monotone lam)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    ∃ (δ : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ), IsUnitary W ∧
      (∀ i, lam i.castSucc ≤ δ i ∧ δ i ≤ lam i.succ) ∧
      (U * diagonal (fun j => (lam j : ℂ)) * Uᴴ).submatrix p.succAbove p.succAbove =
        W * diagonal (fun i => (δ i : ℂ)) * Wᴴ := by
  classical
  let M := Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  let N := Matrix (Fin n) (Fin n) ℂ
  let lam' (t : ℝ) (i : Fin (n + 1)) := lam i + t * (i.val : ℝ)
  let s := lam (Fin.last n) + (n : ℝ)
  let K : Set ((Fin n → ℝ) × N) :=
    (Set.univ.pi (fun _ => Set.Icc (lam 0) s)) ×ˢ {V | IsUnitary V}
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_setOf_isUnitary
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Q : Set ((M × ℝ) × K) := {q |
    (∀ i, lam' q.1.2 i.castSucc ≤ q.2.val.1 i ∧ q.2.val.1 i ≤ lam' q.1.2 i.succ) ∧
    (q.1.1 * diagonal (fun j => (lam' q.1.2 j : ℂ)) * q.1.1ᴴ).submatrix
        p.succAbove p.succAbove =
      q.2.val.2 * diagonal (fun i => (q.2.val.1 i : ℂ)) * q.2.val.2ᴴ}
  have hQ : IsClosed Q := by
    apply IsClosed.inter
    · change IsClosed {q : (M × ℝ) × K | ∀ i : Fin n,
        lam' q.1.2 i.castSucc ≤ q.2.val.1 i ∧ q.2.val.1 i ≤ lam' q.1.2 i.succ}
      rw [Set.setOf_forall]
      apply isClosed_iInter
      intro i
      have hLeft (j : Fin (n + 1)) : Continuous (fun q : (M × ℝ) × K => lam' q.1.2 j) := by
        dsimp only [lam']
        fun_prop
      have hRight : Continuous (fun q : (M × ℝ) × K => q.2.val.1 i) := by
        fun_prop
      exact (isClosed_le (hLeft i.castSucc) hRight).inter (isClosed_le hRight (hLeft i.succ))
    · have hc : Continuous (fun q : (M × ℝ) × K => fun j => (lam' q.1.2 j : ℂ)) := by
        apply continuous_pi
        intro j
        dsimp only [lam']
        fun_prop
      have hd : Continuous (fun q : (M × ℝ) × K => fun j => (q.2.val.1 j : ℂ)) := by
        apply continuous_pi
        intro j
        fun_prop
      have hl : Continuous (fun q : (M × ℝ) × K =>
          q.1.1 * diagonal (fun j => (lam' q.1.2 j : ℂ)) * q.1.1ᴴ) :=
        (((by fun_prop : Continuous (fun q : (M × ℝ) × K => q.1.1)).matrix_mul
          hc.matrix_diagonal).matrix_mul (by fun_prop))
      have hr : Continuous (fun q : (M × ℝ) × K =>
          q.2.val.2 * diagonal (fun j => (q.2.val.1 j : ℂ)) * q.2.val.2ᴴ) :=
        (((by fun_prop : Continuous (fun q : (M × ℝ) × K => q.2.val.2)).matrix_mul
          hd.matrix_diagonal).matrix_mul (by fun_prop))
      exact isClosed_eq (hl.matrix_submatrix p.succAbove p.succAbove) hr
  let A := Prod.fst '' Q
  have hA : IsClosed A := isClosedMap_fst_of_compactSpace _ hQ
  have hmem : (U, 0) ∈ A := by
    apply Classical.byContradiction
    intro hbad
    let O : Set M := {V | (V, (0 : ℝ)) ∉ A}
    have hO : IsOpen O := hA.isOpen_compl.preimage
      (continuous_id.prodMk continuous_const)
    obtain ⟨V, hVbad, hV, hVs⟩ := exists_full_support_unitary_mem_open hO U hU hbad
    let T : Set ℝ := {t | (V, t) ∉ A}
    have hT : IsOpen T := hA.isOpen_compl.preimage
      (continuous_const.prodMk continuous_id)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (show 0 ∈ T from hVbad))
    let t := min ε 1 / 2
    have ht₀ : 0 < t := div_pos (lt_min hε zero_lt_one) (by norm_num)
    have ht₁ : t ≤ 1 := by
      have he := min_le_right ε (1 : ℝ)
      dsimp only [t]
      linarith
    have htε : t < ε := by
      have he := min_le_left ε (1 : ℝ)
      dsimp only [t]
      linarith
    have htT : t ∈ T := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀]
      exact htε)
    have hstrict : StrictMono (lam' t) := by
      intro i j hij
      have hcast : (i.val : ℝ) < j.val := by exact_mod_cast hij
      exact add_lt_add_of_le_of_lt (hlam hij.le) (mul_lt_mul_of_pos_left hcast ht₀)
    obtain ⟨δ, W, hW, hδ, hspec⟩ :=
      exists_strict_interlacing_of_hermitian_compression (lam' t) hstrict V hV p (hVs p)
    have hδK : (δ, W) ∈ K := by
      refine ⟨Set.mem_pi.mpr (fun i _ => ?_), hW⟩
      constructor
      · apply le_trans (hlam (Fin.zero_le i.castSucc))
        exact le_trans (le_add_of_nonneg_right (mul_nonneg ht₀.le (Nat.cast_nonneg _)))
          (hδ i).1.le
      · apply (hδ i).2.le.trans
        have hcast : (i.succ.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ i.succ.isLt)
        exact add_le_add (hlam (Fin.le_last i.succ))
          ((mul_le_of_le_one_left (Nat.cast_nonneg _) ht₁).trans hcast)
    exact htT ⟨((V, t), ⟨(δ, W), hδK⟩), ⟨fun i => ⟨(hδ i).1.le, (hδ i).2.le⟩, hspec⟩, rfl⟩
  obtain ⟨⟨⟨V, t⟩, ⟨⟨δ, W⟩, hδK⟩⟩, hQ, he⟩ := hmem
  cases he
  refine ⟨δ, W, hδK.2, ?_, ?_⟩
  · intro i
    simpa only [lam', zero_mul, add_zero] using hQ.1 i
  · simpa only [lam', zero_mul, add_zero] using hQ.2

end

end MOC
