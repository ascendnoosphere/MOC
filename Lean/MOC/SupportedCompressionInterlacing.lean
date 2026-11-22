import MOC.CompressionCharacteristic
import MOC.HermitianCompressionInterlacing
import MOC.NormalCompressionLine
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-! In a normal principal compression, the touched eigenvalues interlace
on one affine line. All other eigenvalues retain their multiplicities. -/

open BigOperators Matrix Polynomial

namespace MOC

noncomputable section

private theorem eval_affine_deletion_polynomial {r : ℕ}
    (knots w : Fin (r + 1) → ℝ) (μ d : ℂ) (t : ℝ) :
    (∑ i, Polynomial.C (w i : ℂ) *
      ∏ j ∈ Finset.univ.erase i, (X - Polynomial.C (μ + d * (knots j : ℂ)))).eval
        (μ + d * (t : ℂ)) = d ^ r * (deletedRootPolynomial knots w t : ℂ) := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, deletedRootPolynomial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hterm (j : Fin (r + 1)) :
      μ + d * (t : ℂ) - (μ + d * (knots j : ℂ)) = d * ((t : ℂ) - (knots j : ℂ)) := by ring
  simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const]
  have hc : (Finset.univ.erase i).card = r := by
    have h := Finset.card_erase_add_one (Finset.mem_univ i)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hc]
  ring

/-- With distinct supported eigenvalues, the spectrum of a normal
compression has one strictly interlaced value per supported gap, together
with every spectral label where the deleted row vanishes. -/
theorem exists_interlaced_spectral_roots_of_normalCompression {n : ℕ}
    (β : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (p : Fin (n + 1)) (hβ : Set.InjOn β {j | U p j ≠ 0})
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    let S := Finset.univ.filter (fun j => U p j ≠ 0)
    let μ := (U * diagonal β * Uᴴ) p p
    ∃ (r : ℕ) (E : Fin (r + 1) ↪ Fin (n + 1)) (d : ℂ)
      (knots : Fin (r + 1) → ℝ) (α : Fin r → ℝ),
      Finset.univ.map E = S ∧ d ≠ 0 ∧ StrictMono knots ∧
        (∀ j, β (E j) = μ + d * (knots j : ℂ)) ∧
        (∀ i, knots i.castSucc < α i ∧ α i < knots i.succ) ∧
        ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).charpoly.roots =
          (Finset.univ \ S).val.map β +
            (Finset.univ : Finset (Fin r)).val.map (fun i => μ + d * (α i : ℂ)) := by
  classical
  intro S μ
  have hS (j : Fin (n + 1)) : j ∈ S ↔ U p j ≠ 0 := by simp [S]
  have hne : S.Nonempty := by
    by_contra h
    have hz (j : Fin (n + 1)) : U p j = 0 := by
      by_contra hj
      exact h ⟨j, (hS j).mpr hj⟩
    have he := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W p p) hU.1
    simp [Matrix.mul_apply, hz] at he
  have hpos := Finset.card_pos.mpr hne
  obtain ⟨r, hr⟩ : ∃ r, S.card = r + 1 := ⟨S.card - 1, by omega⟩
  let e₀ : Fin (r + 1) ≃ ↥S := (Fintype.equivFinOfCardEq (by simpa using hr)).symm
  obtain ⟨d, hd, hline⟩ := exists_spectral_line_of_normalCompression β U hU p hC
  choose f hf using fun j : ↥S => hline j.val ((hS j.val).mp j.property)
  have hf_inj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    apply hβ ((hS _).mp j.property) ((hS _).mp k.property)
    rw [hf j, hf k, he]
  let f₀ := f ∘ e₀
  let e := (Tuple.sort f₀).trans e₀
  let E := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  let knots := f₀ ∘ Tuple.sort f₀
  have hE : Finset.univ.map E = S := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
      exact (e i).property
    · intro hj
      exact Finset.mem_map.mpr ⟨e.symm ⟨j, hj⟩, Finset.mem_univ _,
        congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)⟩
  have hknots : StrictMono knots := (Tuple.monotone_sort f₀).strictMono_of_injective
    (hf_inj.comp (e₀.injective.comp (Tuple.sort f₀).injective))
  have hparam (j : Fin (r + 1)) : β (E j) = μ + d * (knots j : ℂ) := hf (e j)
  let w (j : Fin (r + 1)) := Complex.normSq (U p (E j))
  have hw (j : Fin (r + 1)) : 0 < w j := Complex.normSq_pos.mpr ((hS _).mp (e j).property)
  obtain ⟨α, hα⟩ := exists_strict_interlaced_roots hknots hw
  refine ⟨r, E, d, knots, α, hE, hd, hknots, hparam, fun i => ⟨(hα i).1, (hα i).2.1⟩, ?_⟩
  let M := (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove
  let Q := ∑ i ∈ S, Polynomial.C (Complex.normSq (U p i) : ℂ) *
    ∏ j ∈ S.erase i, (X - Polynomial.C (β j))
  let αc (i : Fin r) := μ + d * (α i : ℂ)
  have hQmap : Q = ∑ i, Polynomial.C (w i : ℂ) *
      ∏ j ∈ Finset.univ.erase i, (X - Polynomial.C (μ + d * (knots j : ℂ))) := by
    dsimp only [Q]
    rw [← hE, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.map_erase, Finset.prod_map]
    simp only [w, hparam]
  have hQne : Q ≠ 0 := by
    intro hz
    have h := charpoly_principalCompression_support_factorization β U hU p
    change M.charpoly = (∏ j ∈ Finset.univ \ S, (X - Polynomial.C (β j))) * Q at h
    rw [hz, mul_zero] at h
    exact (Matrix.charpoly_monic M).ne_zero h
  have hαroot (i : Fin r) : αc i ∈ Q.roots := by
    apply (Polynomial.mem_roots hQne).mpr
    change Q.eval (μ + d * (α i : ℂ)) = 0
    rw [hQmap, eval_affine_deletion_polynomial, (hα i).2.2, Complex.ofReal_zero, mul_zero]
  have hαmono : StrictMono α := by
    intro i j hij
    have hij' : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    exact (((hα i).2.1.trans_le (hknots.monotone hij')).trans (hα j).1)
  have hαinj : Function.Injective αc := by
    intro i j h
    apply hαmono.injective
    apply Complex.ofReal_injective
    exact mul_left_cancel₀ hd (add_left_cancel h)
  have hroots : M.charpoly.roots = (Finset.univ \ S).val.map β + Q.roots :=
    roots_principalCompression_support_factorization β U hU p
  have hMcard : M.charpoly.roots.card = n := by
    have hc := Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits M.charpoly)
    rw [Polynomial.map_id, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hc
    exact hc.symm
  have hQcard : Q.roots.card = r := by
    have hc := congrArg Multiset.card hroots
    simp only [hMcard, Multiset.card_add, Multiset.card_map, Finset.card_val] at hc
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hs
    omega
  have hn : ((Finset.univ : Finset (Fin r)).val.map αc).Nodup :=
    Multiset.Nodup.map hαinj Finset.univ.nodup
  have hle : (Finset.univ : Finset (Fin r)).val.map αc ≤ Q.roots := by
    apply (Multiset.le_iff_subset hn).2
    intro t ht
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ht
    exact hαroot i
  have heq := Multiset.eq_of_le_of_card_le hle (by simp [hQcard])
  change M.charpoly.roots = (Finset.univ \ S).val.map β +
    (Finset.univ : Finset (Fin r)).val.map αc
  rw [hroots, ← heq]

end

end MOC
