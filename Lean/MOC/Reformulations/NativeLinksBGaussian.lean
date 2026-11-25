import MOC.Claim
import MOC.Geometry
import MOC.Support

/-! Concrete arithmetic spectral restriction for the Dolbeault realization
in Atlas 079. Geometry of complex tori is not used inside this module:
integer real and imaginary parts are kept unchanged, and the comparison
extends by homogeneity and density rather than by arbitrary evaluations. -/

open Matrix BigOperators

namespace MOC.Reformulations.NativeLinksB

noncomputable section

private def rationalComplex (z : ℚ × ℚ) : ℂ :=
  (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

private theorem denseRange_rationalComplex : DenseRange rationalComplex := by
  have hq : DenseRange (Rat.cast : ℚ → ℝ) := Rat.denseRange_cast
  simpa [Function.comp_def, Prod.map_apply, rationalComplex,
    Complex.equivRealProdCLM_symm_apply] using
    Complex.equivRealProdCLM.symm.surjective.denseRange.comp (hq.prodMap hq)
      Complex.equivRealProdCLM.symm.continuous

theorem exists_common_denominator {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ i, ∃ z : ℤ, (d : ℚ) * q i = z := by
  classical
  let d := ∏ i, (q i).den
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun i _ => (q i).den_nz), ?_⟩
  intro i
  obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  change d = (q i).den * e at he
  refine ⟨(e : ℤ) * (q i).num, ?_⟩
  simp only [he, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  rw [mul_assoc, mul_comm (e : ℚ) (q i), ← mul_assoc,
    mul_comm ((q i).den : ℚ) (q i), Rat.mul_den_eq_num, mul_comm]

/-- MOC for genuinely integral Gaussian spectra in every matrix order. -/
def GaussianSpectrumForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℤ × ℤ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun i => (a i).1 + (a i).2 * Complex.I)
      (fun i => (b i).1 + (b i).2 * Complex.I) U

private theorem holds_rationalComplex_of_gaussian (h : GaussianSpectrumForm)
    {n : ℕ} (a b : Fin n → ℚ × ℚ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) : Holds (fun i => rationalComplex (a i)) (fun i => rationalComplex (b i)) U := by
  let p : (Fin n ⊕ Fin n) → ℚ × ℚ := Sum.elim a b
  let q : ((Fin n ⊕ Fin n) × Bool) → ℚ :=
    fun x => if x.2 then (p x.1).1 else (p x.1).2
  obtain ⟨d, hd, hz⟩ := exists_common_denominator q
  choose v hv using hz
  have hEq (i : Fin n ⊕ Fin n) :
      (d : ℂ) * rationalComplex (p i) = v (i, true) + v (i, false) * Complex.I := by
    have hr := congrArg (fun t : ℚ => ((t : ℝ) : ℂ)) (hv (i, true))
    have hi := congrArg (fun t : ℚ => ((t : ℝ) : ℂ)) (hv (i, false))
    simp [q] at hr hi
    simp only [rationalComplex, mul_add, ← mul_assoc]
    rw [hr, hi]
  obtain hscaled := h n (fun i => (v (Sum.inl i, true), v (Sum.inl i, false)))
    (fun i => (v (Sum.inr i, true), v (Sum.inr i, false))) U hU
  have heqa (i : Fin n) := hEq (.inl i)
  have heqb (i : Fin n) := hEq (.inr i)
  change ∀ i, (d : ℂ) * rationalComplex (a i) = _ at heqa
  change ∀ i, (d : ℂ) * rationalComplex (b i) = _ at heqb
  simp only [← heqa, ← heqb] at hscaled
  exact (hull_common_factor_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr hd))
    (determinantValue_scale _ _ U (d : ℂ)) (matchingProduct_scale _ _ (d : ℂ))).mp hscaled

/-- Integral Gaussian endomorphism spectra are a sufficient and necessary
spectral test; the reverse direction is not just the claim for a dense
set assumed as a separate premise. -/
theorem gaussianSpectrumForm_iff : GaussianSpectrumForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    by_contra hf
    rw [holds_iff_directional] at hf
    push_neg at hf
    obtain ⟨η, hstrict⟩ := hf
    let O (σ : Equiv.Perm (Fin n)) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
      {x | (η * matchingProduct x.1 x.2 σ).re < (η * determinantValue x.1 x.2 U).re}
    have ho (σ : Equiv.Perm (Fin n)) : IsOpen (O σ) := by
      unfold O matchingProduct determinantValue
      apply isOpen_lt <;> fun_prop
    have hD : DenseRange (Pi.map (fun _ : Fin n => rationalComplex)) :=
      DenseRange.piMap (fun _ => denseRange_rationalComplex)
    obtain ⟨x, hx⟩ := (hD.prodMap hD).exists_mem_open
      (isOpen_iInter_of_finite ho) ⟨(a, b), Set.mem_iInter.mpr hstrict⟩
    obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp
      (holds_rationalComplex_of_gaussian h x.1 x.2 U hU) η
    have hlt := Set.mem_iInter.mp hx σ
    exact (not_le_of_gt hlt) hσ
  · intro h n a b U hU
    exact h n _ _ U hU

end

end MOC.Reformulations.NativeLinksB
