import MOC.ForestGates
import MOC.HermitianByNormalFourProof

/-! A forest of two-coordinate bridges between normal spectral blocks.
An order-four result controls up to four left ports in each block. -/

open Matrix

open private forestGateMixer_respects_cut twoCoordinateGate_forest_cut
  bridgeRows_one_mul from MOC.ForestGates

namespace MOC

noncomputable section

private theorem holds_forestGateMixer_mul_of_agrees_off_ports
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph κ)
    (hG : G.IsAcyclic) (block : ι → κ) (port : ι → Prop)
    (V : Matrix ι ι ℂ) (hV : IsUnitary V)
    (hVblock : ∀ i j, block i ≠ block j → V i j = 0)
    (a b : ι → ℂ) (gs : List (TwoCoordinateGate ι))
    (hGates : ∀ g ∈ gs, G.Adj (block g.p) (block g.q) ∧ port g.p ∧ port g.q)
    (hDistinct : gs.Pairwise
      (fun g f => s(block g.p, block g.q) ≠ s(block f.p, block f.q)))
    (hBase : ∀ x, (∀ i, ¬ port i → x i = a i) → Holds x b V) :
    ∀ x, (∀ i, ¬ port i → x i = a i) → Holds x b (forestGateMixer gs * V) := by
  classical
  induction gs with
  | nil =>
    intro x hx
    simpa only [forestGateMixer, Matrix.one_mul] using hBase x hx
  | cons g gs ih =>
    intro x hx
    obtain ⟨hd, hgates⟩ := List.pairwise_cons.mp hDistinct
    have hg := hGates g List.mem_cons_self
    let gb : TwoCoordinateGate κ :=
      ⟨block g.p, block g.q, hg.1.ne, g.c, g.s, g.normalized⟩
    obtain ⟨side, hpq, hside⟩ := twoCoordinateGate_forest_cut G hG gb hg.1
    let W := forestGateMixer gs
    have hW := forestGateMixer_unitary gs
    have hWV : IsUnitary (W * V) := by
      let hWs : IsUnitary Wᴴ :=
        ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hW.2,
          by simpa only [Matrix.conjTranspose_conjTranspose] using hW.1⟩
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Wᴴ V hWs hV
    have hWcut := forestGateMixer_respects_cut gs (side ∘ block) (fun f hf =>
      hside _ _ (hGates f (List.mem_cons_of_mem _ hf)).1 (hd f hf).symm)
    have hcut (i j : ι) (hij : (side ∘ block) i ≠ (side ∘ block) j) :
        (W * V) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : (side ∘ block) i = (side ∘ block) k
      · have hkj : block k ≠ block j :=
          fun h => hij (hik.trans (congrArg side h))
        rw [hVblock _ _ hkj, mul_zero]
      · rw [show W i k = 0 from hWcut _ _ hik, zero_mul]
    have htail := ih (fun f hf => hGates f (List.mem_cons_of_mem _ hf)) hgates
    have hswap (i : ι) (hi : ¬ port i) : (x ∘ Equiv.swap g.p g.q) i = a i := by
      have hp : i ≠ g.p := fun h => hi (h.symm ▸ hg.2.1)
      have hq : i ≠ g.q := fun h => hi (h.symm ▸ hg.2.2)
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hp hq, hx i hi]
    have hout := holds_bridgeRows x b (W * V) hWV (side ∘ block) hcut
      hpq g.normalized (htail x hx) (htail _ hswap)
    have hbridge : forestGateMixer (g :: gs) * V =
        bridgeRows (W * V) g.p g.q g.c g.s := by
      change bridgeRows W g.p g.q g.c g.s * V = _
      rw [← bridgeRows_one_mul W g.different, Matrix.mul_assoc,
        bridgeRows_one_mul (W * V) g.different]
    rwa [hbridge]

/-- Join any number of unitary diagonal blocks with two-coordinate gates.
Use each edge of an acyclic graph of blocks at most once. In each block,
one generalized circle contains the right eigenvalues and the negatives
of the left eigenvalues away from a set of at most four gate ports. -/
theorem holds_of_forest_bridges_four_outlier_blocks
    {k : ℕ} {m : Fin k → ℕ} (G : SimpleGraph (Fin k)) (hG : G.IsAcyclic)
    (a b : (j : Fin k) → Fin (m j) → ℂ)
    (ports : (j : Fin k) → Finset (Fin (m j)))
    (hports : ∀ j, (ports j).card ≤ 4)
    (hcircle : ∀ j, SpectrumOnGeneralizedCircle
      (Sum.elim (b j) (fun i : {i // i ∉ ports j} => -a j i.val)))
    (V : (j : Fin k) → Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (hV : ∀ j, IsUnitary (V j)) (gs : List (TwoCoordinateGate (Σ j, Fin (m j))))
    (hGates : ∀ g ∈ gs, G.Adj g.p.1 g.q.1 ∧
      g.p.2 ∈ ports g.p.1 ∧ g.q.2 ∈ ports g.q.1)
    (hDistinct : gs.Pairwise (fun g f => s(g.p.1, g.q.1) ≠ s(f.p.1, f.q.1))) :
    Holds (fun i => a i.1 i.2) (fun i => b i.1 i.2)
      (forestGateMixer gs * Matrix.blockDiagonal' V) := by
  classical
  let W := Matrix.blockDiagonal' V
  have hW : IsUnitary W := by
    constructor
    · simp only [W, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun j => (hV j).1)
    · simp only [W, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun j => (hV j).2)
  have hblock (i j : Σ j, Fin (m j)) (hij : i.1 ≠ j.1) : W i j = 0 := by
    rcases i with ⟨i, x⟩
    rcases j with ⟨j, y⟩
    exact Matrix.blockDiagonal'_apply_ne V x y hij
  let x : (Σ j, Fin (m j)) → ℂ := fun i => a i.1 i.2
  let y : (Σ j, Fin (m j)) → ℂ := fun i => b i.1 i.2
  let port : (Σ j, Fin (m j)) → Prop := fun i => i.2 ∈ ports i.1
  have hbase (x' : (Σ j, Fin (m j)) → ℂ)
      (hx : ∀ i, ¬ port i → x' i = x i) : Holds x' y W := by
    apply holds_of_finite_paired_blocks m (Equiv.refl _) (Equiv.refl _) x' y W V rfl
    intro j
    let f (i : Fin (m j)) := x' ⟨j, i⟩
    change Holds f (b j) (V j)
    apply (holds_swap_iff f (b j) (hV j)).mp
    have hv : IsUnitary (V j)ᴴ :=
      ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using (hV j).2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using (hV j).1⟩
    have he : (Sum.elim (b j) (fun i : {i // i ∉ ports j} => -f i.val)) =
        Sum.elim (b j) (fun i : {i // i ∉ ports j} => -a j i.val) := by
      funext i
      rcases i with i | ⟨i, hi⟩
      · rfl
      · exact congrArg Neg.neg (hx ⟨j, i⟩ hi)
    exact holds_of_common_generalized_circle_with_four_outliers (b j) f (ports j)
      (hports j) (he.symm ▸ hcircle j) (V j)ᴴ hv
  exact holds_forestGateMixer_mul_of_agrees_off_ports G hG Sigma.fst port W hW hblock
    x y gs hGates hDistinct hbase x (fun _ _ => rfl)

end

end MOC
