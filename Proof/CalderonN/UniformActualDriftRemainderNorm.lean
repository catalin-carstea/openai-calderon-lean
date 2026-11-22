module

public import Proof.CalderonN.UniformActualLowerOrderNorm
public import Proof.CalderonN.ActualDriftRemainderFiber
public import Proof.CalderonN.PhysicalTraceCoordinateEnergy
public import Proof.CalderonN.ScaledFirstOrderTraceNorm

import Proof.CalderonN.AngularEnergyDensity
import Proof.CalderonN.PhysicalAngularModelData
import Mathlib.Tactic

/-! The drift applied to the base and lower angular velocity is
bounded directly by the physical test energy. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualSupportedMovingTrace_driftRemainder_bound (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (hg : Elliptic Y K d.γ) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
        (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
        (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
        (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
        (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
        (F : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
        (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
        (v : Field dim) (hv : Test Y d.γ d.frame v) (E : HarmonicTestExpansion Y d.γ d.frame v),
        let hKp := zero_lt_one.trans_le hK
        let b := supportedCoordinateTraceDrift hY hg hKp hr hQ hb
        let P := supportedCoordinateModelDerivative hY hg hKp he hlog hA hEll S
        let W := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
        let F₁ := actualSupportedAffine hY F hF
        let J := movingTraceDriftRemainder b P W F₁
        let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hKp)
        let u := E.traceComponent Complex.reCLM
        let w := E.traceComponent Complex.imCLM
        Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ C/floor*energyNorm Y d v := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨D,hD,hCoord⟩ := uniform_traceCoordinate_scalar_bounds hY hΩ hSub (by omega : 2 ≤ m) K ρ c₀ M Cj hK
  obtain ⟨η₀,U,hη₀,hU,hVel⟩ := uniform_actual_lowerVelocity_coefficient_bounds hn hY hΩ hYc hSub
    hm K ρ c₀ M Cj hK hρ hA hEll S
  obtain ⟨η₁,hη₁,hAdj⟩ := uniform_actualGauss_lowerVelocityFiberAdjoints hn hY hΩ hYc (by omega : 4 ≤ m)
    K ρ c₀ M Cj hK hρ
  let η := min 1 (min η₀ η₁)
  let C := D+(dim:ℝ)*(D*((dim:ℝ)^2*(D*(2*(dim:ℝ)))+D+U))
  let N := 2*(dim:ℝ)*((dim:ℝ)*D+(dim:ℝ)^2*(D*(2*(dim:ℝ))))^2+1
  let J := (Real.sqrt 2*((dim:ℝ)*C+C))*Real.sqrt N
  have hD₀ := zero_le_one.trans hD
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨η,J,lt_min zero_lt_one (lt_min hη₀ hη₁),hJ,?_⟩
  intro floor hFloor ε hε hs d hd hFrame hg he hr hr₀ hlog hQ hb F hC' hF v hv E
  dsimp only
  have hFrame' (x : X dim) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨hSym,hCS,_⟩ := hAdj floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd hFrame F
  have hL := (contDiffOn_actualFirstDensityCenterLinear hΩ hKp hd.1).mono hSub
  have hR := actualGaussScaledConormalFamily_regular hn hY hA hEll S F hCS hL hr hr₀
  have hβ (x : X dim) (hx : x ∈ Y) : floor ≤ beta d.γ d.radius x := (hd.2.2.2.2.1.2 x hx).2.1
  have hs₀ : ε ≤ 1 := hs.trans (min_le_left _ _)
  let G := physicalEnergyDensity d.γ d.frame d.radius v
  let e := fun x => N*G x
  have he' : IntegrableOn e Y :=
    (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hn hY hg hKp d.frame he hFrame' hFloor hv).const_mul N
  let H := Classical.choice (exists_angularModelData hn hY hg hKp d.frame he hFrame' hv.1 E d.radius hlog)
  have hMajor (x : X dim) (hx : x ∈ Y) :
      metricDensity d.γ x*(coordinateTraceEnergy hn (beta d.γ d.radius) (E.traceComponent Complex.reCLM) x+
        coordinateTraceEnergy hn (beta d.γ d.radius) (E.traceComponent Complex.imCLM) x) ≤ e x := by
    obtain ⟨_,_,hEntry,_,hΓ,_⟩ := hCoord floor hFloor ε hs₀ d hd hFrame x hx
    exact physical_coordinateTraceEnergy_le hn hY hg hKp he hFrame' hv E H hx (hFloor.trans (hβ x hx))
      D hD₀ (fun a i => hEntry i a) hΓ
  let S₀ := movingTraceDriftRemainder (supportedCoordinateTraceDrift hY hg hKp hr hQ hb)
    (supportedCoordinateModelDerivative hY hg hKp he hlog hA hEll S)
    (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC' hF)
    (actualSupportedAffine hY F hF)
  have hNorm := norm_scaledFirstOrder_supportedTrace_le hn hY (metricDensity d.γ) (beta d.γ d.radius) e
    (hg.contDiffOn_density hKp) (fun _ _ => Real.sqrt_nonneg _) floor C hFloor hC hβ he'
    (E.traceComponent Complex.reCLM) (E.traceComponent Complex.imCLM) hMajor S₀ (by
      intro x hx
      obtain ⟨_,hk,_,_,hΓ,hl⟩ := hCoord floor hFloor ε hs₀ d hd hFrame x hx
      have hW (i : I dim) := (hVel floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_left _ _)))
        d hd hFrame F hR hSym i
        (actualGaussLowerVelocityFamily_regular hY hg he hr hr₀ hlog hA hEll S F hC' hF hn i) hF x hx).1.angular.bound
      exact actualDriftRemainder_fiber hn hY hg hKp he hr hr₀ hlog hQ hb hA hEll S F hC' hF hx
        (hFloor.trans (hβ x hx)) hD₀ hU (hd.2.2.2.2.1.2 x hx).1.le
        ((hd.2.2.2.2.2 x hx).2.trans hs₀) hk hΓ hl hW)
  dsimp only at hNorm
  refine hNorm.trans_eq ?_
  change _ * Real.sqrt (∫ x in Y,N*G x) = _
  rw [integral_const_mul,Real.sqrt_mul hN,energyNorm,energySq_eq_integral_density]
  dsimp only [J,G]
  ring

end CalderonN
