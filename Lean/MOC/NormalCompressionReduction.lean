import MOC.HermitianCompressionInterlacing
import MOC.NormalCompressionLine
import MOC.PrincipalCoisometry
import Mathlib.Data.Fin.Tuple.Sort

/-! The induction step for a normal pole compression with a fully supported
deleted row and distinct right labels. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- Products on an affine interlace lie in the rectangular hull of the original labels. -/
theorem affine_interlacing_prod_mem_rectangular_hull (a : Fin n → ℂ) (lam : Fin (n + 1) → ℝ)
    (δ : Fin n → ℝ) (hl : ∀ j, lam j.castSucc ≤ δ j) (hu : ∀ j, δ j ≤ lam j.succ)
    (c d : ℂ) (hd : d ≠ 0) :
    (∏ j, (a j + (c + d * (δ j : ℂ)))) ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a (fun j => c + d * (lam j : ℂ)))) := by
  let b (j : Fin n) : ℂ := (a j + c) / d
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ (d ^ n)
  have hterm (j : Fin n) (t : ℝ) :
      d * ((t : ℂ) + b j) = a j + (c + d * (t : ℂ)) := by
    dsimp only [b]
    rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hd]
    ring
  have hprod (t : Fin n → ℝ) : L (∏ j, ((t j : ℂ) + b j)) =
      ∏ j, (a j + (c + d * (t j : ℂ))) := by
    change d ^ n * (∏ j, ((t j : ℂ) + b j)) = _
    simp_rw [← hterm, Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hprod δ]
  apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage L)
    (interlacing_prod_mem_partialMatchingHull lam δ b hl hu)
  rintro _ ⟨e, rfl⟩
  change L (∏ j, ((lam (e j) : ℂ) + b j)) ∈
    convexHull ℝ (Set.range (rectangularMatchingProduct a (fun j => c + d * (lam j : ℂ))))
  have he := hprod (lam ∘ e)
  dsimp only [Function.comp_apply] at he
  rw [he]
  exact subset_convexHull ℝ _ ⟨e, rfl⟩

private theorem affine_interlacing_matching_hull (a : Fin n → ℂ) (lam : Fin (n + 1) → ℝ)
    (δ : Fin n → ℝ) (hl : ∀ j, lam j.castSucc ≤ δ j) (hu : ∀ j, δ j ≤ lam j.succ)
    (c d : ℂ) (hd : d ≠ 0) :
    convexHull ℝ (Set.range (matchingProduct a (fun j => c + d * (δ j : ℂ)))) ⊆
      convexHull ℝ (Set.range (rectangularMatchingProduct a (fun j => c + d * (lam j : ℂ)))) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨σ, rfl⟩
  apply convexHull_mono _ (affine_interlacing_prod_mem_rectangular_hull (a ∘ σ) lam δ hl hu c d hd)
  rintro _ ⟨e, rfl⟩
  refine ⟨σ.symm.toEmbedding.trans e, ?_⟩
  change (∏ i, (a i + (c + d * (lam (e (σ.symm i)) : ℂ)))) =
    ∏ j, (a (σ j) + (c + d * (lam (e j) : ℂ)))
  rw [← Equiv.prod_comp σ (fun i => a i + (c + d * (lam (e (σ.symm i)) : ℂ)))]
  simp only [Equiv.symm_apply_apply]

private theorem affine_diagonal_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (W : Matrix ι ι ℂ) (hW : IsUnitary W) (c d : ℂ) :
    W * diagonal (fun j => c + d * (a j : ℂ)) * Wᴴ =
      c • (1 : Matrix ι ι ℂ) + d • (W * diagonal (fun j => (a j : ℂ)) * Wᴴ) := by
  have hconst : diagonal (fun _ : ι => c) = c • (1 : Matrix ι ι ℂ) := by
    ext i j : 1
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hscale : diagonal (fun j => d * (a j : ℂ)) = d • diagonal (fun j => (a j : ℂ)) := by
    change diagonal (d • (fun j => (a j : ℂ))) = _
    exact Matrix.diagonal_smul d (fun j => (a j : ℂ))
  rw [← Matrix.diagonal_add (fun _ => c) (fun j => d * (a j : ℂ)), hconst, hscale]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.1]

/-- The smaller-order conjecture covers a normal principal compression when
the right spectrum is simple and the deleted row has full support. -/
theorem holds_normal_compression_of_fullSupport (hSmall : Conjecture (Fin n))
    (a : Fin n → ℂ) (β : Fin (n + 1) → ℂ) (hβ : Function.Injective β)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hrow : ∀ j, U p j ≠ 0)
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    (diagonal a + (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a β)) := by
  classical
  let c := (U * diagonal β * Uᴴ) p p
  obtain ⟨d, hd, hline⟩ := exists_spectral_line_of_normalCompression β U hU p hC
  choose f hf using fun j => hline j (hrow j)
  have hparam (j : Fin (n + 1)) : β j = c + d * (f j : ℂ) := hf j
  have hinj : Function.Injective f := by
    intro i j h
    apply hβ
    rw [hparam i, hparam j, h]
  let e := Tuple.sort f
  let lam := f ∘ e
  have hlam : StrictMono lam := (Tuple.monotone_sort f).strictMono_of_injective (hinj.comp e.injective)
  let V := U.submatrix (Equiv.refl _) e
  have hV : IsUnitary V := unitary_reindex (Equiv.refl _) e hU
  have hVrow (j : Fin (n + 1)) : V p j ≠ 0 := hrow (e j)
  have hrelabel : V * diagonal (β ∘ e) * Vᴴ = U * diagonal β * Uᴴ := by
    dsimp only [V]
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv β e,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] <;> rfl
  have hβline : β ∘ e = fun j => c + d * (lam j : ℂ) := funext fun j => hparam (e j)
  obtain ⟨δ, W, hW, hδ, hspec⟩ := exists_strict_interlacing_of_hermitian_compression lam hlam V hV p hVrow
  have hcomp : (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove =
      W * diagonal (fun j => c + d * (δ j : ℂ)) * Wᴴ := by
    rw [← hrelabel, hβline, affine_diagonal_conjugation lam V hV c d, affine_diagonal_conjugation δ W hW c d]
    change c • ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix p.succAbove p.succAbove) +
      d • ((V * diagonal (fun j => (lam j : ℂ)) * Vᴴ).submatrix p.succAbove p.succAbove) = _
    rw [Matrix.submatrix_one p.succAbove Fin.succAbove_right_injective, hspec]
  have hlow := hSmall a (fun j => c + d * (δ j : ℂ)) W hW
  unfold Holds determinantValue at hlow
  rw [← hcomp] at hlow
  have hinter := affine_interlacing_matching_hull a lam δ (fun j => (hδ j).1.le)
    (fun j => (hδ j).2.le) c d hd hlow
  rw [← hβline] at hinter
  apply convexHull_mono ?_ hinter
  rintro _ ⟨s, rfl⟩
  exact ⟨s.trans e.toEmbedding, rfl⟩

end

end MOC
