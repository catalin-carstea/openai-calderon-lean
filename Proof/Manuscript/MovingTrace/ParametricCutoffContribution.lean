module

public import Proof.Manuscript.MovingTrace.ParametricTaylorGapContribution
import all Proof.CalderonPatch.BoundaryLayerCutoffEstimate
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2400000

open CalderonPaper Set Finset
open CalderonN (X I axis)
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

/-- In a fixed collar the derivatives of the normal cutoff are supported
at a positive depth. Both commutator profiles have arbitrary decay in h. -/
def cutoffContribution (a : P × X n → ℂ) (η : ℝ → ℝ) (τ : (P × X n) × ℝ → ℂ)
    (j : ℕ) (h : ℝ) (q : (P × X n) × ℝ) : ℂ :=
  scaledProfileContribution
    (fun p => -((deriv (deriv η) p.2 : ℝ) : ℂ) + τ p / 2 * ((deriv η p.2 : ℝ) : ℂ))
    B.kappa (B.layerJetPolynomial a j (.inl ())) (j+2) h q +
  scaledProfileContribution (fun p => -2 * ((deriv η p.2 : ℝ) : ℂ))
    B.kappa (B.layerJetPolynomial a j (.inr (.inl ()))) (j+1) h q

theorem cutoffContribution_envelope
    (hU : IsOpen U) {K K₀ : Set (P × X n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hK₀ : IsClosed K₀) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K₀, a q = 0)
    {O J : Set ((P × X n) × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    (hJK : ∀ q ∈ J, q.1 ∈ K)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (τ : (P × X n) × ℝ → ℂ) (hτ : ContDiffOn ℝ ∞ τ O)
    {d : ℝ} (hd : 0 < d)
    (hzero : ∀ q ∈ O, q.2 < d → deriv η q.2 = 0 ∧ deriv (deriv η) q.2 = 0)
    (j m N : ℕ) :
    SmoothCollarContribution J (B.cutoffContribution a η τ j) N (fun h => h^m * h⁻¹^N) := by
  obtain ⟨c,hc,hck⟩ := exists_positive_lower_bound_on_compact hK
    (B.kappa_smooth.continuousOn.mono hKU) (fun q hq => B.kappa_pos q (hKU hq))
  have hη1 : ContDiff ℝ ∞ (deriv η) :=
    (hη.of_le (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).deriv'
  have hη2 : ContDiff ℝ ∞ (deriv (deriv η)) :=
    (hη1.of_le (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).deriv'
  have hη1C : ContDiffOn ℝ ∞ (fun q : (P × X n) × ℝ => ((deriv η q.2 : ℝ) : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp (hη1.comp contDiff_snd)).contDiffOn
  have hη2C : ContDiffOn ℝ ∞ (fun q : (P × X n) × ℝ => ((deriv (deriv η) q.2 : ℝ) : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp (hη2.comp contDiff_snd)).contDiffOn
  have hContribution {f : (P × X n) × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f O)
      (hf0 : ∀ q ∈ O, q.2 < d → f q = 0) (i : LayerJetIndex n) (k : ℕ) :
      SmoothCollarContribution J (scaledProfileContribution f B.kappa (B.layerJetPolynomial a j i) k)
        N (fun h => h^m * h⁻¹^N) :=
    SmoothCollarContribution.separated_profile hU hK hKU hO hJ hJO hJK hf hd hf0
      B.kappa_smooth hc hck (B.layerJetPolynomial_regular hU hK₀ a ha ha0 j i) (2*j+3)
      (fun q hq => Nat.lt_succ_of_le (B.layerJetPolynomial_degree hU hK₀ a ha ha0 j i hq)) k m N
  unfold cutoffContribution
  apply SmoothCollarContribution.add
  · apply hContribution (hη2C.neg.add ((hτ.div_const 2).mul hη1C))
    intro q hq hq'
    obtain ⟨h1,h2⟩ := hzero q hq hq'
    simp [h1,h2]
  · apply hContribution (contDiffOn_const.mul hη1C)
    intro q hq hq'
    simp [(hzero q hq hq').1]

theorem cutoffContribution_slice
    (hU : IsOpen U) (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) (a : P × X n → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (η : ℝ → ℝ) (τ : (P × X n) × ℝ → ℂ) (j : ℕ) (h : ℝ)
    {x : X n} (hx : x ∈ slice U p) (t : ℝ) :
    B.cutoffContribution a η τ j h ((p,x),t) =
      (h : ℂ)^j * scaledCutoffDefect (τ ((p,x),t)) η h
        ((B.angularSlice p ξ hξ).profile (fun y => a (p,y)) j) x t := by
  let C := B.angularSlice p ξ hξ
  have hSlice (i : LayerJetIndex n) :
      B.layerJetPolynomial a j i (p,x) =
        C.layerJetPolynomial (fun y => a (p,y)) j i x :=
    B.layerJetPolynomial_slice hU p ξ hξ hAxis hK ha ha0 j i hx
  unfold cutoffContribution scaledProfileContribution scaledCutoffDefect polynomialProfileFamily
  dsimp only
  rw [hSlice (.inl ()), hSlice (.inr (.inl ()))]
  change (h : ℂ)^(j+2) * (_ * C.profile (fun y => a (p,y)) j (x,t/h)) +
    (h : ℂ)^(j+1) * (_ * polynomialProfile (C.kappa x)
      (C.layerJetPolynomial (fun y => a (p,y)) j (.inr (.inl ())) x) (t/h)) = _
  rw [C.layerJet_normal_read]
  simp only [pow_add,pow_one]
  ring

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
