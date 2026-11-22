module

public import Proof.CalderonN.UniformActualLowerVelocityBounds
public import Proof.CalderonN.UniformActualLowerVelocityFiberAdjoints
public import Proof.CalderonN.PhysicalLowerOrderFiberEstimate
public import Proof.CalderonN.UniformTraceCoordinateBounds

import Mathlib.Tactic

/-! The genuine lower-order operator satisfies the inverse-floor
bound in the frozen physical test norm. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualSupportedMovingTrace_lowerOrder_bound (hn : 3 ≤ dim)
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
        let a := supportedPrincipalTraceCoeff hY hr hQ
        let b := supportedCoordinateTraceDrift hY hg hKp hr hQ hb
        let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
        let P := supportedCoordinateModelDerivative hY hg hKp he hlog hA hEll S
        let W := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
        let F₁ := actualSupportedAffine hY F hF
        let J := movingTraceLowerOrder a b V P W F₁
        let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hKp)
        let u := E.traceComponent Complex.reCLM
        let w := E.traceComponent Complex.imCLM
        Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ C/floor*energyNorm Y d v := by
  have hKp := zero_lt_one.trans_le hK
  let B₀ := smoothTraceFlatDegree hA hEll S
  obtain ⟨C,hC,hRaise⟩ := smoothTraceRaising_uniform_angularBound hn
  have hFlat := smoothTraceDegree_angularBound hn B₀ (smoothTraceFlatDegree_symmetric hn hA hEll S)
    (smoothTraceFlatDegree_finite hA hEll S)
  obtain ⟨D,hD,hCoord⟩ := uniform_traceCoordinate_scalar_bounds hY hΩ hSub (by omega : 2 ≤ m) K ρ c₀ M Cj hK
  obtain ⟨η₀,U,hη₀,hU,hVel⟩ := uniform_actual_lowerVelocity_coefficient_bounds hn hY hΩ hYc hSub
    hm K ρ c₀ M Cj hK hρ hA hEll S
  obtain ⟨η₁,hη₁,hAdj⟩ := uniform_actualGauss_lowerVelocityFiberAdjoints hn hY hΩ hYc (by omega : 4 ≤ m)
    K ρ c₀ M Cj hK hρ
  let η := min 1 (min η₀ η₁)
  let R := (dim:ℝ)*(D*C)
  let T := (dim:ℝ)*(D*C+D*R)
  let W := U+(dim:ℝ)^2*(D*U)+D*U
  let C₀ := (dim:ℝ)^2*(D*(T+(R*U+U*R))+D*W)+(dim:ℝ)*(D*R)
  have hD₀ := zero_le_one.trans hD
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀,R,T,W]; positivity
  refine ⟨η,C₀,lt_min zero_lt_one (lt_min hη₀ hη₁),hC₀,?_⟩
  intro floor hFloor ε hε hs d hd hFrame hg he hr hr₀ hlog hQ hb F hC' hF v hv E
  dsimp only
  have hFrame' (x : X dim) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨hSym,hCS,hG⟩ := hAdj floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd hFrame F
  have hL := (contDiffOn_actualFirstDensityCenterLinear hΩ hKp hd.1).mono hSub
  have hR := actualGaussScaledConormalFamily_regular hn hY hA hEll S F hCS hL hr hr₀
  have hAdj' (i : I dim) := (hG hg he hA hEll S i).2
  choose G hGReg hGAdj using hAdj' 
  let J := movingTraceLowerOrder (supportedPrincipalTraceCoeff hY hr hQ)
    (supportedCoordinateTraceDrift hY hg hKp hr hQ hb)
    (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S)
    (supportedCoordinateModelDerivative hY hg hKp he hlog hA hEll S)
    (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC' hF)
    (actualSupportedAffine hY F hF)
  have hFib (x : X dim) (hx : x ∈ Y) : SupportedTraceFiberBound hn x 1 C₀ J := by
    let β := beta d.γ d.radius x
    have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
    have hrp := (hd.2.2.2.2.1.2 x hx).1.le
    have hrβ : d.radius x*β ≤ 1 := by
      calc
        d.radius x*β ≤ d.radius x*β^2 := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg (show 0 ≤ β from zero_le_one.trans hβ) (sub_nonneg.mpr hβ)]) hrp
        _ ≤ ε := (hd.2.2.2.2.2 x hx).2
        _ ≤ 1 := hs.trans (min_le_left _ _)
    obtain ⟨hQ₁,hk,hEntry,hDEntry,hΓ,hl⟩ := hCoord floor hFloor ε (hs.trans (min_le_left _ _)) d hd hFrame x hx
    have hW (i : I dim) := (hVel floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_left _ _)))
      d hd hFrame F hR hSym i
      (actualGaussLowerVelocityFamily_regular hY hg he hr hr₀ hlog hA hEll S F hC' hF hn i) hF x hx)
    exact actualSupportedMovingTrace_lowerOrder_fiber_bound hn hY hg hKp he hFrame' hr hr₀ hlog hQ hb
      hA hEll S F hC' hF hx hβ hC hD₀ hU hrp hrβ hQ₁ hk hEntry hDEntry hΓ hl (hRaise B₀ hFlat)
      (fun i => (hW i).2) G hGReg hGAdj (fun i => (hW i).1)
  exact physicalTrace_lowerOrder_bound_of_fiber_angularBounds hn hY hg hKp he hFrame'
    hd.2.2.2.2.1 hFloor hv E J C₀ hC₀ hFib

end CalderonN
