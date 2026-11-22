module

public import Proof.Manuscript.MovingTrace.ParametricTrialWave
public import Proof.Manuscript.MovingTrace.SmoothProfileContribution
public import Proof.Manuscript.MovingTrace.CollarTaylorGap
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2200000

open CalderonPaper Set Finset
open CalderonN (X I axis)
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

abbrev RemainderMatrix (n : ℕ) (P : Type*) := ((P × X n) × ℝ) → Matrix (I n) (I n) ℂ
abbrev RemainderDrift (n : ℕ) (P : Type*) := ((P × X n) × ℝ) → I n → ℂ

/-- The normal Taylor gap multiplies each bounded profile by an additional
normal monomial. Rescaling the monomial makes the full gap power explicit. -/
def depthMomentPolynomial (a : P × X n → ℂ) (j m : ℕ) (i : LayerJetIndex n) (q : P × X n) :
    Polynomial ℂ :=
  Polynomial.X ^ m * B.layerJetPolynomial a j i q

/-- The coefficient Taylor remainder in the dephased residual of one
transport profile. Each term is a smooth unscaled amplitude times a
polynomial in scaled depth times the decaying root exponential. -/
def taylorGapContribution (a : P × X n → ℂ) (j m : ℕ)
    (A : RemainderMatrix n P) (τ : (P × X n) × ℝ → ℂ) (c : RemainderDrift n P)
    (h : ℝ) (q : (P × X n) × ℝ) : ℂ :=
  (∑ i : I n, ∑ l : I n,
    scaledProfileContribution
      (fun p => A p i l * B.covector i p.1 * B.covector l p.1)
      B.kappa (B.depthMomentPolynomial a j m (.inl ())) (j+m) h q) +
  scaledProfileContribution (fun p => τ p / 2)
    B.kappa (B.depthMomentPolynomial a j m (.inr (.inl ()))) (j+m+1) h q +
  (∑ i : I n, ∑ l : I n,
    scaledProfileContribution
      (fun p => -2 * Complex.I * A p i l * B.covector i p.1)
      B.kappa (B.depthMomentPolynomial a j m (.inr (.inr (.inl l)))) (j+m+1) h q) +
  (∑ i : I n,
    scaledProfileContribution (fun p => -Complex.I * c p i * B.covector i p.1)
      B.kappa (B.depthMomentPolynomial a j m (.inl ())) (j+m+1) h q) +
  (∑ i : I n, ∑ l : I n,
    scaledProfileContribution (fun p => -A p i l)
      B.kappa (B.depthMomentPolynomial a j m (.inr (.inr (.inr (i,l))))) (j+m+2) h q) +
  ∑ i : I n,
    scaledProfileContribution (fun p => -c p i)
      B.kappa (B.depthMomentPolynomial a j m (.inr (.inr (.inl i)))) (j+m+2) h q

theorem taylorGapContribution_envelope
    (hU : IsOpen U) {K K₀ : Set (P × X n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hK₀ : IsClosed K₀) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K₀, a q = 0)
    {O J : Set ((P × X n) × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    (hJK : ∀ q ∈ J, q.1 ∈ K) (hOU : O ⊆ U ×ˢ (univ : Set ℝ))
    (A : RemainderMatrix n P) (hA : ∀ i l, ContDiffOn ℝ ∞ (fun p => A p i l) O)
    (τ : (P × X n) × ℝ → ℂ) (hτ : ContDiffOn ℝ ∞ τ O)
    (c : RemainderDrift n P) (hc : ∀ i, ContDiffOn ℝ ∞ (fun p => c p i) O)
    (j m N : ℕ) :
    SmoothCollarContribution J (B.taylorGapContribution a j m A τ c) N
      (fun h => h^m * h⁻¹^N) := by
  obtain ⟨d,hd,hdk⟩ := exists_positive_lower_bound_on_compact hK
    (B.kappa_smooth.continuousOn.mono hKU) (fun q hq => B.kappa_pos q (hKU hq))
  have hCov (i : I n) : ContDiffOn ℝ ∞ (fun p : (P × X n) × ℝ => B.covector i p.1) O :=
    (B.covector_smooth i).comp contDiffOn_fst (fun p hp => (hOU hp).1)
  have hP (i : LayerJetIndex n) : CoeffContDiffOn (B.depthMomentPolynomial a j m i) U :=
    (CoeffContDiffOn.const (Polynomial.X ^ m) U).mul (B.layerJetPolynomial_regular hU hK₀ a ha ha0 j i)
  have hD (i : LayerJetIndex n) (q : P × X n) (hq : q ∈ U) :
      (B.depthMomentPolynomial a j m i q).natDegree < m+2*j+3 := by
    have h := B.layerJetPolynomial_degree hU hK₀ a ha ha0 j i hq
    exact Nat.lt_succ_of_le ((Polynomial.natDegree_mul_le.trans
      (add_le_add (Polynomial.natDegree_X_pow_le m) h)).trans (by omega))
  have hContribution {f : (P × X n) × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f O)
      (i : LayerJetIndex n) (k : ℕ) (hkm : m ≤ k) :
      SmoothCollarContribution J (scaledProfileContribution f B.kappa (B.depthMomentPolynomial a j m i) k)
        N (fun h => h^m * h⁻¹^N) :=
    SmoothCollarContribution.profile hU hK hKU hO hJ hJO hJK hf B.kappa_smooth hd hdk
      (hP i) (m+2*j+3) (hD i) k m N hkm
  unfold taylorGapContribution
  refine (((((SmoothCollarContribution.sum univ fun i _ => SmoothCollarContribution.sum univ
    fun l _ => hContribution (((hA i l).mul (hCov i)).mul (hCov l)) (.inl ()) _ (by omega)).add
      (hContribution (hτ.div_const 2) (.inr (.inl ())) _ (by omega))).add
      (SmoothCollarContribution.sum univ fun i _ => SmoothCollarContribution.sum univ
        fun l _ => hContribution ((contDiffOn_const.mul (hA i l)).mul (hCov i))
          (.inr (.inr (.inl l))) _ (by omega))).add
      (SmoothCollarContribution.sum univ fun i _ =>
        hContribution ((contDiffOn_const.mul (hc i)).mul (hCov i)) (.inl ()) _ (by omega))).add
      (SmoothCollarContribution.sum univ fun i _ => SmoothCollarContribution.sum univ
        fun l _ => hContribution (hA i l).neg (.inr (.inr (.inr (i,l)))) _ (by omega))).add
      (SmoothCollarContribution.sum univ fun i _ =>
        hContribution (hc i).neg (.inr (.inr (.inl i))) _ (by omega))

/-- Converting the scaled normal monomial back to physical depth yields
the exact scalar coefficient difference on a fixed parameter slice. -/
theorem taylorGapContribution_slice
    (hU : IsOpen U) (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) (a : P × X n → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (A : RemainderMatrix n P) (τ : (P × X n) × ℝ → ℂ) (c : RemainderDrift n P)
    (j m : ℕ) {h : ℝ} (hh : h ≠ 0) {x : X n} (hx : x ∈ slice U p) (t : ℝ) :
    let q := ((p,x),t)
    let z := (t : ℂ)^m
    B.taylorGapContribution a j m A τ c h q =
      (h : ℂ)^j * scalarCoefficientDifference (z • A q) (z * τ q) (z • c q) ξ h
        ((B.angularSlice p ξ hξ).profile (fun y => a (p,y)) j) x (t/h) := by
  dsimp only
  let C := B.angularSlice p ξ hξ
  let V := C.profile (fun y => a (p,y)) j
  let q := ((p,x),t)
  let s := t/h
  let z := (t : ℂ)^m
  let d := (h : ℂ)^j * z
  let R (i : LayerJetIndex n) :=
    polynomialProfile (C.kappa x) (C.layerJetPolynomial (fun y => a (p,y)) j i x) s
  have hR (f : (P × X n) × ℝ → ℂ) (i : LayerJetIndex n) (k : ℕ) :
      scaledProfileContribution f B.kappa (B.depthMomentPolynomial a j m i) (j+m+k) h q =
        (d * (h : ℂ)^k) * f q * R i := by
    have hs : (h : ℂ) * (s : ℂ) = (t : ℂ) := by
      exact_mod_cast (mul_div_cancel₀ t hh)
    have hs' : (h : ℂ)^m * (s : ℂ)^m = z := by rw [← mul_pow, hs]
    unfold scaledProfileContribution depthMomentPolynomial polynomialProfileFamily
    change (h : ℂ)^(j+m+k) * (f q *
      (Real.exp (-B.kappa (p,x) * s) •
        (Polynomial.X^m * B.layerJetPolynomial a j i (p,x)).eval (s : ℂ))) = _
    rw [B.layerJetPolynomial_slice hU p ξ hξ hAxis hK ha ha0 j i hx]
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Complex.real_smul,pow_add]
    change (h : ℂ)^j * (h : ℂ)^m * (h : ℂ)^k *
      (f q * ((Real.exp (-C.kappa x * s) : ℂ) *
        ((s : ℂ)^m * (C.layerJetPolynomial (fun y => a (p,y)) j i x).eval (s : ℂ)))) = _
    have hgroup :
        (h : ℂ)^j * (h : ℂ)^m * (h : ℂ)^k *
          (f q * ((Real.exp (-C.kappa x * s) : ℂ) *
            ((s : ℂ)^m * (C.layerJetPolynomial (fun y => a (p,y)) j i x).eval (s : ℂ)))) =
        (h : ℂ)^j * ((h : ℂ)^m * (s : ℂ)^m) * (h : ℂ)^k * f q * R i := by
      unfold R polynomialProfile
      simp only [Complex.real_smul]
      ring
    rw [hgroup, hs']
  have h0 : R (.inl ()) = V (x,s) := rfl
  have hn : R (.inr (.inl ())) = splitNormal V x s := C.layerJet_normal_read _ j x s
  have ht (i : I n) : R (.inr (.inr (.inl i))) = splitFirst V x s i :=
    C.layerJet_tangent_read (isOpen_slice hU p) (isClosed_slice hK p)
      (fun y => a (p,y)) (contDiffOn_slice ha p) (fun y hy => ha0 (p,y) hy) j hx s i
  have h₂ (i l : I n) : R (.inr (.inr (.inr (i,l)))) = splitSecond V x s i l :=
    C.layerJet_second_read (isOpen_slice hU p) (isClosed_slice hK p)
      (fun y => a (p,y)) (contDiffOn_slice ha p) (fun y hy => ha0 (p,y) hy) j hx s i l
  change B.taylorGapContribution a j m A τ c h q =
    (h : ℂ)^j * scalarCoefficientDifference (z • A q) (z * τ q) (z • c q) ξ h V x s
  rw [scalarCoefficientDifference_scale_all, ← mul_assoc]
  change _ = d * scalarCoefficientDifference (A q) (τ q) (c q) ξ h V x s
  unfold taylorGapContribution
  have hR0 (f : (P × X n) × ℝ → ℂ) (i : LayerJetIndex n) :
      scaledProfileContribution f B.kappa (B.depthMomentPolynomial a j m i) (j+m) h q =
        d * f q * R i := by simpa using hR f i 0
  simp only [hR0, hR, pow_one, h0, hn, ht, h₂, show q.1 = (p,x) by rfl, hξ]
  unfold scalarCoefficientDifference
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, mul_sub]
  -- The six profiles are the six terms of the scalar coefficient variation.
  ring_nf
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
