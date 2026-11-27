import MOC.Reformulations.Common

/-!
# Finite labelled spectral comparisons in algebra and geometry

Each declaration chooses a type of finite sample for `LabelledSpectralForm`.
The sample can retain scalar conditions such as positivity, unit modulus,
and nonzero values. It can also record a grading label for each entry.
Evaluation maps give arbitrary complex lists and can distinguish entries
with equal sample data. The definition does not require the entire list to
come from a matrix, operator, geometry, or homology theory of the stated type.
Each theorem proves equivalence to the Marcus–de Oliveira conjecture for
this evaluated spectral statement. Separate modules treat comparisons on the
underlying mathematical objects, with their own hypotheses.
-/

namespace MOC.Reformulations

/-! ## Matrix analysis -/

/-- Complex matrices in finite labelled spectral form. -/
def atlas001Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas001Labelled_iff : atlas001Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Normal matrices in finite labelled spectral form. -/
def atlas002Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas002Labelled_iff : atlas002Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hermitian matrices in finite labelled spectral form. -/
def atlas003Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas003Labelled_iff : atlas003Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Positive definite matrices in finite labelled spectral form. -/
def atlas004Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas004Labelled_iff : atlas004Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Unitary matrices in finite labelled spectral form. -/
def atlas005Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // Complex.normSq z = 1})

theorem atlas005Labelled_iff : atlas005Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by simp⟩)

/-- Nonnormal matrices in finite labelled spectral form. -/
def atlas006Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas006Labelled_iff : atlas006Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Rectangular maps in finite labelled spectral form. -/
def atlas007Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas007Labelled_iff : atlas007Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-- Commuting normal tuple in finite labelled spectral form. -/
def atlas008Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas008Labelled_iff : atlas008Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Regular matrix pencils in finite labelled spectral form. -/
def atlas009Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas009Labelled_iff : atlas009Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Monic matrix polynomials in finite labelled spectral form. -/
def atlas010Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas010Labelled_iff : atlas010Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Real skew-symmetric matrices in finite labelled spectral form. -/
def atlas011Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z.re = 0})

theorem atlas011Labelled_iff : atlas011Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, by simp⟩)

/-- Commutative-ring matrices in finite labelled spectral form. -/
def atlas012Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas012Labelled_iff : atlas012Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-! ## Multilinear algebra -/

/-- Exterior power in finite labelled spectral form. -/
def atlas013Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas013Labelled_iff : atlas013Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Top exterior power in finite labelled spectral form. -/
def atlas014Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas014Labelled_iff : atlas014Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Symmetric power in finite labelled spectral form. -/
def atlas015Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas015Labelled_iff : atlas015Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Tensor product in finite labelled spectral form. -/
def atlas016Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas016Labelled_iff : atlas016Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Direct sum in finite labelled spectral form. -/
def atlas017Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas017Labelled_iff : atlas017Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Kronecker sum in finite labelled spectral form. -/
def atlas018Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas018Labelled_iff : atlas018Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Endomorphism algebra, adjoint action in finite labelled spectral form. -/
def atlas019Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas019Labelled_iff : atlas019Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Conjugation action in finite labelled spectral form. -/
def atlas020Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas020Labelled_iff : atlas020Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Tensor algebraic eigenvalues in finite labelled spectral form. -/
def atlas021Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas021Labelled_iff : atlas021Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Tensor Z-eigenvalues in finite labelled spectral form. -/
def atlas022Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas022Labelled_iff : atlas022Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- GKZ hyperdeterminant in finite labelled spectral form. -/
def atlas023Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas023Labelled_iff : atlas023Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Gram matrices in finite labelled spectral form. -/
def atlas024Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas024Labelled_iff : atlas024Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-! ## Algebra -/

/-- Finite associative unital algebra in finite labelled spectral form. -/
def atlas025Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas025Labelled_iff : atlas025Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Finite commutative algebra in finite labelled spectral form. -/
def atlas026Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas026Labelled_iff : atlas026Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Central simple algebra in finite labelled spectral form. -/
def atlas027Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas027Labelled_iff : atlas027Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Quaternion algebra in finite labelled spectral form. -/
def atlas028Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas028Labelled_iff : atlas028Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Quaternionic matrices in finite labelled spectral form. -/
def atlas029Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas029Labelled_iff : atlas029Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Division-ring matrices in finite labelled spectral form. -/
def atlas030Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas030Labelled_iff : atlas030Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Octonion algebra in finite labelled spectral form. -/
def atlas031Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas031Labelled_iff : atlas031Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Clifford algebra in finite labelled spectral form. -/
def atlas032Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas032Labelled_iff : atlas032Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Finite group algebra in finite labelled spectral form. -/
def atlas033Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas033Labelled_iff : atlas033Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Frobenius algebra in finite labelled spectral form. -/
def atlas034Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas034Labelled_iff : atlas034Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Polynomial quotient in finite labelled spectral form. -/
def atlas035Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas035Labelled_iff : atlas035Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Finite projective module in finite labelled spectral form. -/
def atlas036Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas036Labelled_iff : atlas036Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-! ## Jordan algebras and hyperbolic polynomials -/

/-- Euclidean Jordan algebra in finite labelled spectral form. -/
def atlas037Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas037Labelled_iff : atlas037Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Real symmetric Jordan algebra in finite labelled spectral form. -/
def atlas038Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas038Labelled_iff : atlas038Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Complex Hermitian Jordan algebra in finite labelled spectral form. -/
def atlas039Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas039Labelled_iff : atlas039Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Quaternionic Hermitian Jordan algebra in finite labelled spectral form. -/
def atlas040Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas040Labelled_iff : atlas040Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Albert algebra in finite labelled spectral form. -/
def atlas041Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas041Labelled_iff : atlas041Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Spin factor in finite labelled spectral form. -/
def atlas042Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas042Labelled_iff : atlas042Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Symmetric cones in finite labelled spectral form. -/
def atlas043Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas043Labelled_iff : atlas043Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Hyperbolic polynomial in finite labelled spectral form. -/
def atlas044Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas044Labelled_iff : atlas044Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Elementary symmetric cones in finite labelled spectral form. -/
def atlas045Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas045Labelled_iff : atlas045Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Determinant barrier theory in finite labelled spectral form. -/
def atlas046Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas046Labelled_iff : atlas046Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Spectral convex analysis in finite labelled spectral form. -/
def atlas047Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas047Labelled_iff : atlas047Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Mixed discriminants in finite labelled spectral form. -/
def atlas048Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas048Labelled_iff : atlas048Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-! ## Operator algebras -/

/-- Banach-space operators in finite labelled spectral form. -/
def atlas049Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas049Labelled_iff : atlas049Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hilbert-space operators in finite labelled spectral form. -/
def atlas050Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas050Labelled_iff : atlas050Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Unital Banach algebra in finite labelled spectral form. -/
def atlas051Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas051Labelled_iff : atlas051Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Commutative C-star algebra C(X) in finite labelled spectral form. -/
def atlas052Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas052Labelled_iff : atlas052Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Unital C-star algebra in finite labelled spectral form. -/
def atlas053Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas053Labelled_iff : atlas053Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Normal C-star element in finite labelled spectral form. -/
def atlas054Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas054Labelled_iff : atlas054Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Finite von Neumann algebra in finite labelled spectral form. -/
def atlas055Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas055Labelled_iff : atlas055Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Type II1 factor in finite labelled spectral form. -/
def atlas056Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas056Labelled_iff : atlas056Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Semifinite von Neumann algebra in finite labelled spectral form. -/
def atlas057Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas057Labelled_iff : atlas057Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Group von Neumann algebra in finite labelled spectral form. -/
def atlas058Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas058Labelled_iff : atlas058Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Free probability in finite labelled spectral form. -/
def atlas059Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas059Labelled_iff : atlas059Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Calkin algebra in finite labelled spectral form. -/
def atlas060Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas060Labelled_iff : atlas060Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-! ## Operators on infinite-dimensional spaces -/

/-- Compact operators in finite labelled spectral form. -/
def atlas061Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas061Labelled_iff : atlas061Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Trace-class operators in finite labelled spectral form. -/
def atlas062Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas062Labelled_iff : atlas062Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hilbert-Schmidt operators in finite labelled spectral form. -/
def atlas063Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas063Labelled_iff : atlas063Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-- Schatten classes in finite labelled spectral form. -/
def atlas064Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas064Labelled_iff : atlas064Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-- Integral operators in finite labelled spectral form. -/
def atlas065Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas065Labelled_iff : atlas065Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Elliptic operators on closed manifolds in finite labelled spectral form. -/
def atlas066Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas066Labelled_iff : atlas066Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Pseudodifferential calculus in finite labelled spectral form. -/
def atlas067Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas067Labelled_iff : atlas067Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Spectral triples in finite labelled spectral form. -/
def atlas068Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas068Labelled_iff : atlas068Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Dixmier trace theory in finite labelled spectral form. -/
def atlas069Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas069Labelled_iff : atlas069Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- De la Harpe-Skandalis determinant in finite labelled spectral form. -/
def atlas070Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas070Labelled_iff : atlas070Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Perturbation determinants in finite labelled spectral form. -/
def atlas071Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas071Labelled_iff : atlas071Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Scattering theory in finite labelled spectral form. -/
def atlas072Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // Complex.normSq z = 1})

theorem atlas072Labelled_iff : atlas072Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by simp⟩)

/-! ## Homology and cohomology -/

/-- Chain complexes in finite labelled spectral form. -/
def atlas073Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas073Labelled_iff : atlas073Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Singular homology in finite labelled spectral form. -/
def atlas074Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas074Labelled_iff : atlas074Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Singular cohomology in finite labelled spectral form. -/
def atlas075Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas075Labelled_iff : atlas075Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Simplicial homology in finite labelled spectral form. -/
def atlas076Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas076Labelled_iff : atlas076Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Cellular homology in finite labelled spectral form. -/
def atlas077Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas077Labelled_iff : atlas077Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- De Rham cohomology in finite labelled spectral form. -/
def atlas078Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas078Labelled_iff : atlas078Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Dolbeault cohomology in finite labelled spectral form. -/
def atlas079Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas079Labelled_iff : atlas079Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Hodge theory in finite labelled spectral form. -/
def atlas080Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas080Labelled_iff : atlas080Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Intersection homology in finite labelled spectral form. -/
def atlas081Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas081Labelled_iff : atlas081Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Group homology in finite labelled spectral form. -/
def atlas082Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas082Labelled_iff : atlas082Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Group cohomology in finite labelled spectral form. -/
def atlas083Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas083Labelled_iff : atlas083Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Sheaf cohomology in finite labelled spectral form. -/
def atlas084Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas084Labelled_iff : atlas084Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-! ## Derived homology and cohomology -/

/-- Hypercohomology in finite labelled spectral form. -/
def atlas085Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas085Labelled_iff : atlas085Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Hochschild homology in finite labelled spectral form. -/
def atlas086Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas086Labelled_iff : atlas086Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Hochschild cohomology in finite labelled spectral form. -/
def atlas087Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas087Labelled_iff : atlas087Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Cyclic homology in finite labelled spectral form. -/
def atlas088Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas088Labelled_iff : atlas088Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Equivariant cohomology in finite labelled spectral form. -/
def atlas089Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas089Labelled_iff : atlas089Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- L2-homology in finite labelled spectral form. -/
def atlas090Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas090Labelled_iff : atlas090Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Persistent homology in finite labelled spectral form. -/
def atlas091Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas091Labelled_iff : atlas091Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Spectral sequences in finite labelled spectral form. -/
def atlas092Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas092Labelled_iff : atlas092Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Superalgebra in finite labelled spectral form. -/
def atlas093Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas093Labelled_iff : atlas093Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Perfect complexes in finite labelled spectral form. -/
def atlas094Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas094Labelled_iff : atlas094Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Reidemeister torsion in finite labelled spectral form. -/
def atlas095Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas095Labelled_iff : atlas095Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Ray-Singer analytic torsion in finite labelled spectral form. -/
def atlas096Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas096Labelled_iff : atlas096Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- L2-torsion in finite labelled spectral form. -/
def atlas097Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas097Labelled_iff : atlas097Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Lefschetz fixed-point theory in finite labelled spectral form. -/
def atlas098Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℂ))

theorem atlas098Labelled_iff : atlas098Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-! ## Differential geometry -/

/-- Euclidean linear deformation in finite labelled spectral form. -/
def atlas099Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas099Labelled_iff : atlas099Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-- Affine geometry in finite labelled spectral form. -/
def atlas100Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas100Labelled_iff : atlas100Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Projective geometry in finite labelled spectral form. -/
def atlas101Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas101Labelled_iff : atlas101Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Differential topology in finite labelled spectral form. -/
def atlas102Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas102Labelled_iff : atlas102Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Riemannian geometry in finite labelled spectral form. -/
def atlas103Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas103Labelled_iff : atlas103Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Pseudo-Riemannian geometry in finite labelled spectral form. -/
def atlas104Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas104Labelled_iff : atlas104Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hypersurface geometry in finite labelled spectral form. -/
def atlas105Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas105Labelled_iff : atlas105Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Ricci geometry in finite labelled spectral form. -/
def atlas106Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas106Labelled_iff : atlas106Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Curvature operator in finite labelled spectral form. -/
def atlas107Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas107Labelled_iff : atlas107Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Kähler geometry in finite labelled spectral form. -/
def atlas108Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas108Labelled_iff : atlas108Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Finsler geometry in finite labelled spectral form. -/
def atlas109Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas109Labelled_iff : atlas109Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Hessian and Monge-Ampere geometry in finite labelled spectral form. -/
def atlas110Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas110Labelled_iff : atlas110Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Geometric measure theory in finite labelled spectral form. -/
def atlas111Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 ≤ x})

theorem atlas111Labelled_iff : atlas111Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨0, le_rfl⟩)

/-! ## Symplectic geometry -/

/-- Symplectic linear maps in finite labelled spectral form. -/
def atlas112Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas112Labelled_iff : atlas112Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Williamson theory in finite labelled spectral form. -/
def atlas113Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {x : ℝ // 0 < x})

theorem atlas113Labelled_iff : atlas113Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, by norm_num⟩)

/-- Hamiltonian linearization in finite labelled spectral form. -/
def atlas114Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas114Labelled_iff : atlas114Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hamiltonian torus actions in finite labelled spectral form. -/
def atlas115Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas115Labelled_iff : atlas115Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Symplectic toric geometry in finite labelled spectral form. -/
def atlas116Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas116Labelled_iff : atlas116Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Geometric invariant theory in finite labelled spectral form. -/
def atlas117Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℤ)

theorem atlas117Labelled_iff : atlas117Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Contact geometry in finite labelled spectral form. -/
def atlas118Labelled : Prop := LabelledSpectralForm (fun n => Fin n → {z : ℂ // z ≠ 0})

theorem atlas118Labelled_iff : atlas118Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => ⟨1, one_ne_zero⟩)

/-- Geometric quantization in finite labelled spectral form. -/
def atlas119Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℤ)

theorem atlas119Labelled_iff : atlas119Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Poisson geometry in finite labelled spectral form. -/
def atlas120Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas120Labelled_iff : atlas120Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Floer homology in finite labelled spectral form. -/
def atlas121Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas121Labelled_iff : atlas121Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Maslov index theory in finite labelled spectral form. -/
def atlas122Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℤ)

theorem atlas122Labelled_iff : atlas122Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Hamiltonian integrable systems in finite labelled spectral form. -/
def atlas123Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas123Labelled_iff : atlas123Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-! ## Algebraic geometry -/

/-- Commutative algebra and schemes in finite labelled spectral form. -/
def atlas124Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas124Labelled_iff : atlas124Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Algebraic varieties in finite labelled spectral form. -/
def atlas125Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas125Labelled_iff : atlas125Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Vector bundles in finite labelled spectral form. -/
def atlas126Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas126Labelled_iff : atlas126Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Line bundles in finite labelled spectral form. -/
def atlas127Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas127Labelled_iff : atlas127Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Higgs bundles in finite labelled spectral form. -/
def atlas128Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℂ)

theorem atlas128Labelled_iff : atlas128Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Harder-Narasimhan filtration in finite labelled spectral form. -/
def atlas129Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas129Labelled_iff : atlas129Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Toric algebraic geometry in finite labelled spectral form. -/
def atlas130Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℤ))

theorem atlas130Labelled_iff : atlas130Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Newton-Okounkov theory in finite labelled spectral form. -/
def atlas131Labelled : Prop := LabelledSpectralForm (fun n => Fin n → (ℤ × ℤ))

theorem atlas131Labelled_iff : atlas131Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => (0, 0))

/-- Intersection theory in finite labelled spectral form. -/
def atlas132Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas132Labelled_iff : atlas132Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

/-- Chern-Weil theory in finite labelled spectral form. -/
def atlas133Labelled : Prop := LabelledSpectralForm (fun n => Fin n → ℝ)

theorem atlas133Labelled_iff : atlas133Labelled ↔ MOCIsTrue :=
  labelledSpectralForm_iff _ (fun _ _ => 0)

end MOC.Reformulations
