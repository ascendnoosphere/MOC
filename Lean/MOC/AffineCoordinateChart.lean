import MOC.FiniteCurvePrimitiveCoordinate
import MOC.FiniteCurveRootBranches

/-! An actual affine chart recovered from one simple plane root. -/

open Set Filter MvPolynomial
open scoped Topology BigOperators

namespace MOC

/-- Denominator-cleared coordinate recovery and a simple root of the
plane model provide an actual local holomorphic section of the old
projection. The section agrees with all affine points near the start. -/
theorem exists_local_holomorphic_affine_coordinate_chart
    {σ : Type*} (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (P : Polynomial (Polynomial ℂ))
    (hplane : ∀ a b, (P.map (Polynomial.evalRingHom a)).IsRoot b ↔
      ∃ x ∈ zeroLocus Q, eval x t = a ∧ eval x u = b)
    (d : σ → Polynomial ℂ) (E : σ → Polynomial (Polynomial ℂ))
    (hrec : ∀ i : σ, f (d i) * Ideal.Quotient.mk Q (X i) =
      (E i).eval₂ f.toRingHom (Ideal.Quotient.mk Q u))
    (x₀ : zeroLocus Q)
    (hden : ∀ᶠ a in 𝓝 (eval x₀.val t), ∀ i, (d i).eval a ≠ 0)
    (hsimp : (P.map (Polynomial.evalRingHom (eval x₀.val t))).derivative.eval (eval x₀.val u) ≠ 0) :
    ∃ H : ℂ → σ → ℂ, H (eval x₀.val t) = x₀.val ∧
      (∀ᶠ a in 𝓝 (eval x₀.val t), H a ∈ zeroLocus Q ∧ eval (H a) t = a ∧
        ∀ i, DifferentiableAt ℂ (fun z => H z i) a) ∧
      ∀ᶠ x : zeroLocus Q in 𝓝 x₀, H (eval x.val t) = x.val := by
  have eval_eq (x : zeroLocus Q) (i : σ) :
      (d i).eval (eval x.val t) * x.val i =
        (E i).eval₂ (Polynomial.evalRingHom (eval x.val t)) (eval x.val u) := by
    let φ : (MvPolynomial σ ℂ ⧸ Q) →ₐ[ℂ] ℂ :=
      Ideal.Quotient.liftₐ Q (MvPolynomial.aeval x.val) fun a ha =>
        (mem_zeroLocus_iff.mp x.property) a ha
    have hφ (a : MvPolynomial σ ℂ) : φ (Ideal.Quotient.mk Q a) = eval x.val a := rfl
    have he : φ.comp f = Polynomial.aeval (eval x.val t) := by
      apply Polynomial.algHom_ext
      change φ (f Polynomial.X) = Polynomial.aeval (eval x.val t) Polynomial.X
      rw [← ht, hφ, Polynomial.aeval_X]
    have hh : φ.toRingHom.comp f.toRingHom = Polynomial.evalRingHom (eval x.val t) :=
      congrArg AlgHom.toRingHom he
    have hd' : φ (f (d i)) = (d i).eval (eval x.val t) := by
      have h := congrArg (fun g : Polynomial ℂ →+* ℂ => g (d i)) hh
      exact h
    have h := congrArg φ (hrec i)
    rw [map_mul, hd', hφ, MvPolynomial.eval_X] at h
    have heval := Polynomial.hom_eval₂ (E i) f.toRingHom φ.toRingHom (Ideal.Quotient.mk Q u)
    rw [hh] at heval
    change φ _ = _ at heval
    have hu : φ.toRingHom (Ideal.Quotient.mk Q u) = eval x.val u := hφ u
    rw [hu] at heval
    rw [heval] at h
    exact h
  have hroot (x : zeroLocus Q) :
      (P.map (Polynomial.evalRingHom (eval x.val t))).IsRoot (eval x.val u) :=
    (hplane _ _).mpr ⟨x.val, x.property, rfl, rfl⟩
  obtain ⟨b, hb, hh, hUnique⟩ :=
    exists_local_holomorphic_simple_root P (eval x₀.val t) (eval x₀.val u) (hroot x₀) hsimp
  let H (a : ℂ) (i : σ) := (E i).eval₂ (Polynomial.evalRingHom a) (b a) / (d i).eval a
  have H_eq (x : zeroLocus Q) (hu : b (eval x.val t) = eval x.val u)
      (hd : ∀ i, (d i).eval (eval x.val t) ≠ 0) : H (eval x.val t) = x.val := by
    funext i
    dsimp only [H]
    rw [hu, ← eval_eq x i, mul_comm, mul_div_cancel_right₀ _ (hd i)]
  refine ⟨H, H_eq x₀ hb hden.self_of_nhds, ?_, ?_⟩
  · filter_upwards [hden, hh] with a hd ha
    obtain ⟨x, hx, ht', hu'⟩ := (hplane a (b a)).mp ha.1
    have hX : H a = x :=
      ht' ▸ H_eq ⟨x,hx⟩ (by simpa only [ht'] using hu'.symm) (by simpa only [ht'] using hd)
    refine ⟨hX.symm ▸ hx, hX.symm ▸ ht', fun i => ?_⟩
    apply DifferentiableAt.div _ (d i).differentiableAt (hd i)
    simp_rw [Polynomial.eval₂_eq_sum_range]
    exact DifferentiableAt.sum (fun k hk =>
      ((E i).coeff k).differentiableAt.mul (ha.2.pow k))
  · have hc : ContinuousAt (fun x : zeroLocus Q => (eval x.val t, eval x.val u)) x₀ :=
      ((t.continuous_eval.comp continuous_subtype_val).prodMk
        (u.continuous_eval.comp continuous_subtype_val)).continuousAt
    have hd : ContinuousAt (fun x : zeroLocus Q => eval x.val t) x₀ := hc.fst
    filter_upwards [hc.eventually hUnique, hd.eventually hden] with x hx hx'
    exact H_eq x (hx (hroot x)).symm hx'


/-- Reverse a genuine holomorphic affine chart using the two simple
plane roots of the old coordinate and the gap. The resulting section
lies on the original affine curve and is locally inverse to the gap. -/
theorem exists_local_holomorphic_gap_chart_of_simple_plane_pair
    {σ : Type*} (Q : Ideal (MvPolynomial σ ℂ))
    (t g : MvPolynomial σ ℂ) (P R : Polynomial (Polynomial ℂ))
    (hP : ∀ x : zeroLocus Q, (P.map (Polynomial.evalRingHom (eval x.val t))).IsRoot (eval x.val g))
    (hR : ∀ a w, (R.map (Polynomial.evalRingHom w)).IsRoot a ↔
      (P.map (Polynomial.evalRingHom a)).IsRoot w)
    (x₀ : zeroLocus Q)
    (hPs : (P.map (Polynomial.evalRingHom (eval x₀.val t))).derivative.eval (eval x₀.val g) ≠ 0)
    (hRs : (R.map (Polynomial.evalRingHom (eval x₀.val g))).derivative.eval (eval x₀.val t) ≠ 0)
    (H : ℂ → σ → ℂ) (h₀ : H (eval x₀.val t) = x₀.val)
    (hH : ∀ᶠ a in 𝓝 (eval x₀.val t), H a ∈ zeroLocus Q ∧ eval (H a) t = a ∧
      ∀ i, DifferentiableAt ℂ (fun z => H z i) a)
    (hInv : ∀ᶠ x : zeroLocus Q in 𝓝 x₀, H (eval x.val t) = x.val) :
    ∃ J : ℂ → σ → ℂ, J (eval x₀.val g) = x₀.val ∧
      (∀ᶠ w in 𝓝 (eval x₀.val g), J w ∈ zeroLocus Q ∧ eval (J w) g = w ∧
        ∀ i, DifferentiableAt ℂ (fun z => J z i) w) ∧
      ∀ᶠ x : zeroLocus Q in 𝓝 x₀, J (eval x.val g) = x.val := by
  let a₀ := eval x₀.val t
  let w₀ := eval x₀.val g
  obtain ⟨p, hp, _, hpu⟩ := exists_local_holomorphic_simple_root P a₀ w₀ (hP x₀) hPs
  obtain ⟨b, hb, hbN, hbu⟩ :=
    exists_local_holomorphic_simple_root R w₀ a₀ ((hR a₀ w₀).mpr (hP x₀)) hRs
  have hbCont : ContinuousAt b w₀ := hbN.self_of_nhds.2.continuousAt
  have hHa : ContinuousAt H a₀ := by
    exact continuousAt_pi.mpr (fun i => (hH.self_of_nhds.2.2 i).continuousAt)
  have hGH : ContinuousAt (fun a => eval (H a) g) a₀ := g.continuous_eval.continuousAt.comp hHa
  let J (w : ℂ) := H (b w)
  have hbH : Tendsto b (𝓝 w₀) (𝓝 a₀) := by
    change Tendsto b (𝓝 w₀) (𝓝 (b w₀)) at hbCont
    rwa [hb] at hbCont
  have hcc₁ : Tendsto (fun w : ℂ => (b w, w)) (𝓝 w₀) (𝓝 (a₀,w₀)) := by
    rw [nhds_prod_eq]
    exact hbH.prodMk tendsto_id
  have hcc₂ : Tendsto (fun w : ℂ => (b w, eval (H (b w)) g)) (𝓝 w₀) (𝓝 (a₀,w₀)) := by
    rw [nhds_prod_eq]
    have hGT : Tendsto (fun a => eval (H a) g) (𝓝 a₀) (𝓝 w₀) := by
      change Tendsto (fun a => eval (H a) g) (𝓝 a₀) (𝓝 (eval (H a₀) g)) at hGH
      rwa [show H a₀ = x₀.val from h₀] at hGH
    exact hbH.prodMk (hGT.comp hbH)
  refine ⟨J, ?_, ?_, ?_⟩
  · change H (b w₀) = x₀.val
    rw [hb]
    exact h₀
  · filter_upwards [hbN, hbH.eventually hH, hcc₁.eventually hpu, hcc₂.eventually hpu]
      with w hw hJw hu₁ hu₂
    have hroot : (P.map (Polynomial.evalRingHom (b w))).IsRoot (eval (J w) g) := by
      have h := hP ⟨J w,hJw.1⟩
      simpa only [show eval (J w) t = b w from hJw.2.1] using h
    refine ⟨hJw.1, ?_, fun i => (hJw.2.2 i).comp w hw.2⟩
    exact (hu₂ hroot).trans (hu₁ ((hR (b w) w).mp hw.1)).symm
  · have hc : ContinuousAt (fun x : zeroLocus Q => (eval x.val g, eval x.val t)) x₀ :=
      ((g.continuous_eval.comp continuous_subtype_val).prodMk
        (t.continuous_eval.comp continuous_subtype_val)).continuousAt
    filter_upwards [hc.eventually hbu, hInv] with x hx hi
    have he := hx ((hR (eval x.val t) (eval x.val g)).mpr (hP x))
    change eval x.val t = b (eval x.val g) at he
    simpa only [J, ← he] using hi


end MOC
