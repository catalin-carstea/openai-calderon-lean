module

public import Proof.CalderonN.UniformActualDriftRemainderNorm
public import Proof.CalderonN.MovingTraceTwoComponentComparison
public import Proof.CalderonN.ActualMovingTraceComparison
public import Proof.CalderonN.UniformActualGaussPairedAdjoints

import Proof.CalderonN.ActualMovingTracePairedAdjoint
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.PhysicalEnergyFrameInvariance
import Mathlib.Tactic

/-! The uniform principal perturbation form estimate is the remaining input
needed for the physical coercivity theorem. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def ActualMovingTracePrincipalErrorEstimate (hn : 3 ≤ dim) (hY : IsOpen Y)
    {K : ℝ} (hK : 0 < K)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (d : Data dim) (ε C : ℝ) : Prop :=
  ∀ (hg : Elliptic Y K d.γ) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    (v : Field dim), Test Y d.γ d.frame v → ∀ (H : HarmonicTestExpansion Y d.γ d.frame v)
    (Ud : Module.End ℝ (SmoothSupportedTraceSection Y)),
    let T := physicalRaisingModel hY hg hK he hlog hA hEll S
    let L := physicalLoweringModel hY hg hK he hlog hA hEll S
    let Td := L-physicalTraceModelCorrection hY he hA hEll S hlog
    let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hK)
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let U := movingTracePerturbation a (a-g) 0 V D E F₁
    let u := H.traceComponent Complex.reCLM
    let w := H.traceComponent Complex.imCLM
    PairedAdjoint B U Ud →
      |movingTraceAdjointErrorForm B T Td L U Ud u+movingTraceAdjointErrorForm B T Td L U Ud w| ≤
        C*ε*energySq Y d.γ d.frame d.radius v

theorem uniformEstimate_of_actualMovingTracePrincipalError (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hError : ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ActualMovingTracePrincipalErrorEstimate hn hY (zero_lt_one.trans_le hK) hA hEll S d ε C) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  have hKp := zero_lt_one.trans_le hK
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨η₁,hη₁,hData⟩ := uniform_exists_actualGaussFiberData (Y:=Y) hn₂ hΩ (by omega : 4 ≤ m)
    K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,hη₂,hReg⟩ := uniform_actualGauss_lowerVelocityFiberAdjoints hn hY hΩ hYc (by omega : 4 ≤ m)
    K ρ c₀ M Cj hK hρ
  obtain ⟨η₃,hη₃,hPair⟩ := uniform_actualGauss_pairedAdjoints hn hY hΩ hYc (by omega : 4 ≤ m)
    K ρ c₀ M Cj hK hρ
  obtain ⟨η₄,J₀,hη₄,hJ₀,hJ⟩ := uniform_actualSupportedMovingTrace_lowerOrder_bound hn hY hΩ hYc hSub
    hm K ρ c₀ M Cj hK hρ hA hEll S
  obtain ⟨η₅,J₁,hη₅,hJ₁,hDrift⟩ := uniform_actualSupportedMovingTrace_driftRemainder_bound hn hY hΩ hYc hSub
    hm K ρ c₀ M Cj hK hρ hA hEll S
  let τ := min η (min η₁ (min η₂ (min η₃ (min η₄ (min η₅ (ρ/4))))))
  have hτ : 0 < τ := lt_min hη (lt_min hη₁ (lt_min hη₂ (lt_min hη₃ (lt_min hη₄ (lt_min hη₅ (by positivity))))))
  suffices h : ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
      ∀ (d : Data dim) ε, 0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d →
        (∀ x i,d.frame x i = smoothMetricFrame (d.γ x) i) →
        ∀ v, Test Y d.γ d.frame v → energyNorm Y d v ≤ C*traceNorm Y d v by
    obtain ⟨floor,ε₀,C,hfloor,hε₀,hC',h⟩ := h
    exact ⟨floor,ε₀,C,hfloor,hε₀,hC',uniformEstimate_of_canonicalFrames hn hY hΩ hSub K ρ c₀ M Cj hKp
      floor ε₀ C h⟩
  apply uniformEstimate_of_movingTrace_comparison_on hn hY hΩ hSub (by omega : 2 ≤ m) K ρ c₀ M Cj hK hc₀
    (F₀:=1) hτ hC (add_nonneg hJ₀ hJ₁) (fun d => ∀ x i,d.frame x i = smoothMetricFrame (d.γ x) i)
  intro floor hFloor ε hε hs d hd hFrame v hv H D
  have hs₀ := hs.trans (min_le_right _ _)
  have hs₁ := hs₀.trans (min_le_right _ _)
  have hs₂ := hs₁.trans (min_le_right _ _)
  have hs₃ := hs₂.trans (min_le_right _ _)
  have hs₄ := hs₃.trans (min_le_right _ _)
  let F (x : X dim) (hx : x ∈ Y) :=
    Classical.choice (hData floor hFloor ε hε (hs₀.trans (min_le_left _ _)) d hd x hx)
  have hγ : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg₂ : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I dim) := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hframe (x : X dim) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hr := hd.2.2.2.2.1.1
  have hr₀ (x : X dim) (hx : x ∈ Y) := (hd.2.2.2.2.1.2 x hx).1.ne'
  have hlog := hr.log hr₀
  have hQ (i j : I dim) := contDiffOn_principal_entry (hγ.smoothMetric hKp) (hg₂.smoothMetric hKp) i j
  have hb (i : I dim) := contDiffOn_drift_entry hY (hγ.smoothMetric hKp) (hg₂.smoothMetric hKp) i
  obtain ⟨_,_,hReg'⟩ := hReg floor hFloor ε hε (hs₁.trans (min_le_left _ _)) d hd hFrame F
  have hC' (i : I dim) := (hReg' hγ he hA hEll S i).1
  have hDensity := (contDiffOn_actualFirstDensityCenterLinear hΩ hKp hd.1).mono hSub
  have hF' (i : I dim) := actualGaussAffineFamily_regular hn hY hγ he hr hDensity hA hEll S F i
  let μ := metricDensity d.γ
  have hμ := hγ.contDiffOn_density hKp
  have hAdj (i : I dim) := hPair floor hFloor ε hε (hs₂.trans (min_le_left _ _)) d hd hFrame
    F i (hC' i) μ hμ
  let B := smoothSupportedTracePairingL hn hY μ hμ
  have hZero (i : I dim) : PairedAdjoint B ((0 : I dim → Module.End ℝ (SmoothSupportedTraceSection Y)) i)
      ((0 : I dim → Module.End ℝ (SmoothSupportedTraceSection Y)) i) := by
    intro u w
    simp only [Pi.zero_apply,LinearMap.zero_apply,map_zero]
  obtain ⟨Ud,hUd⟩ := exists_pairedAdjoint_actualMovingTracePerturbation_of_paired_drift hn hY hγ hKp he hr hr₀ hlog
    hQ hA hEll S F hC' hF' hDensity μ hμ (fun _ hx => metricDensity_pos hγ hKp hx) 0 hZero hAdj
  have hρ' (x : X dim) (hx : x ∈ Y) : 2*d.radius x < ρ := by
    have hrp := (hd.2.2.2.2.1.2 x hx).1.le
    have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
    have hR := (le_mul_of_one_le_right hrp (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 x hx).2
    linarith [hR,hs₄.trans (min_le_right _ _)]
  have hMatch (i : I dim) := actualGaussFiber_matches hn₂ hY hΩ hd hKp hρ' F i
  have hErr := hError floor hFloor ε hε (hs.trans (min_le_left _ _)) d hd hFrame
    hγ he hr hr₀ hlog hQ F hC' hF' v hv H Ud hUd
  have hLow := hJ floor hFloor ε hε (hs₃.trans (min_le_left _ _)) d hd hFrame
    hγ he hr hr₀ hlog hQ hb F hC' hF' v hv H
  have hLowDrift := hDrift floor hFloor ε hε (hs₄.trans (min_le_left _ _)) d hd hFrame
    hγ he hr hr₀ hlog hQ hb F hC' hF' v hv H
  dsimp only at hLow hLowDrift
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let b := supportedCoordinateTraceDrift hY hγ hKp hr hQ hb
  let V := supportedLeadingTraceVelocity hY hγ he hr hr₀ hA hEll S
  let P := supportedCoordinateModelDerivative hY hγ hKp he hlog hA hEll S
  let E := actualSupportedGaussRemainder hY hγ he hr hr₀ hlog hA hEll S F hC' hF'
  let F₁ := actualSupportedAffine hY F hF'
  let J := movingTraceLowerOrder a b V P E F₁
  let Jd := movingTraceDriftRemainder b P E F₁
  let u := H.traceComponent Complex.reCLM
  let w := H.traceComponent Complex.imCLM
  have hJ' : Real.sqrt (B ((J+Jd) u) ((J+Jd) u)+B ((J+Jd) w) ((J+Jd) w)) ≤
      (J₀+J₁)/floor*energyNorm Y d v := by
    rw [LinearMap.add_apply,LinearMap.add_apply]
    refine (sqrt_twoComponent_pairing_add_le B (smoothSupportedTracePairing_symm hn μ)
      (smoothSupportedTracePairing_self_nonneg hn μ (fun _ => Real.sqrt_nonneg _)) (J u) (J w) (Jd u) (Jd w)).trans ?_
    exact (add_le_add hLow hLowDrift).trans_eq (by rw [add_div,add_mul])
  exact actualSupportedMovingTrace_comparison_drift_split hn hY hγ hKp he hframe hd.2.2.2.1
    hr hr₀ hlog hQ hb hA hEll S F hC' hF' (fun i => (hMatch i).1) (fun i => (hMatch i).2)
    hv.1 H D Ud _ _ hUd hErr hJ'

end CalderonN
