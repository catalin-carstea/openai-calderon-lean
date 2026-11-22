module

public import Proof.CalderonN.ActualErrorCoercivityCaller
public import Proof.CalderonN.UniformActualPrincipalTraceBounds
public import Proof.CalderonN.ActualPrincipalTraceDivergenceMatch
public import Proof.CalderonN.CoordinatePrincipalErrorBound

import Proof.CalderonN.PhysicalAngularModelData
import Proof.CalderonN.AngularEnergyDensity
import Mathlib.Tactic

/-! The actual principal perturbation satisfies the integrated error
form estimate of Proposition 5.3. The remaining drift has already
been absorbed directly in the physical norm. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5900000
set_option maxSynthPendingDepth 31
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualMovingTracePrincipalError (hn : 3 ≤ dim) :
    UniformActualMovingTracePrincipalError hn := by
  intro Y Ω hY hΩ hYc hYΩ
  have hSub := subset_closure.trans hYΩ
  refine ⟨8,le_rfl,?_⟩
  intro K ρ c₀ M Cj hK hρ hc₀ S
  have hKp := zero_lt_one.trans_le hK
  let A : X dim → Mat dim := fun _ => 1
  have hA : ContDiff ℝ ∞ A := contDiff_const
  have hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A 1 1 :=
    uniformlyEllipticOn_const_one_one (n:=Fin dim) _
  obtain ⟨η₀,C,D,hη₀,hC,hD,hUniform⟩ := uniform_actualCoordinatePrincipalTrace_bounds hn hY hΩ hYc hSub
    (by decide : 8 ≤ 8) K ρ c₀ M Cj hK hρ hA hEll S
  obtain ⟨η₁,hη₁,hReg⟩ := uniform_actualGauss_lowerVelocityFiberAdjoints hn hY hΩ hYc
    (by decide : 4 ≤ 8) K ρ c₀ M Cj hK hρ
  obtain ⟨E,hE,hCoord⟩ := uniform_traceCoordinate_scalar_bounds hY hΩ hSub (by decide : 2 ≤ 8)
    K ρ c₀ M Cj hK
  let η := min 1 (min η₀ η₁)
  let N := 2*(dim:ℝ)*((dim:ℝ)*E+(dim:ℝ)^2*(E*(2*(dim:ℝ))))^2+1
  let Λ := 5*coordinatePrincipalCommConstant dim C+4*(2*(dim:ℝ)^2+2*(dim:ℝ)+1)
  let C₀ := 2*Λ*C*D*N
  have hE₀ := zero_le_one.trans hE
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hΛ : 0 ≤ Λ := by dsimp only [Λ,coordinatePrincipalCommConstant]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨η,C₀,lt_min zero_lt_one (lt_min hη₀ hη₁),hC₀,?_⟩
  intro floor hFloor ε hε hs d hd hFrame
  intro hg he hr hr₀ hlog hQ F hCF hFF v hv Xv Ud
  dsimp only
  intro hUd
  have hFrame' (x : X dim) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hg₂ : SmoothMetric Y d.g₂ :=
    (show Elliptic Y K d.g₂ from
      ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩).smoothMetric hKp
  have hs₀ := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs₁ := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs₂ : ε ≤ 1 := hs.trans (min_le_left _ _)
  obtain ⟨hSym,hCS,_⟩ := hReg floor hFloor ε hε hs₁ d hd hFrame F
  have hDensity := (contDiffOn_actualFirstDensityCenterLinear hΩ hKp hd.1).mono hSub
  have hR := actualGaussScaledConormalFamily_regular hn hY hA hEll S F hCS hDensity hr hr₀
  obtain ⟨V,hV,hLocal⟩ := hUniform floor hFloor ε hε hs₀ d hd hFrame hg he hr hr₀ hlog hQ hg₂ F hR hSym
  let P := actualCoordinatePrincipalTraceFactors hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S V
  let U := P.divergence hY
  let T := CoordinateTraceFirstOrder.ofPaired (P.model.first hY) (P.model.zero hY)
  let Td := CoordinateTraceFirstOrder.ofPairedAdjoint hY U.density (P.model.first hY) (P.model.zero hY)
  let Z := (P.model.correction hY).forward
  let μ := metricDensity d.γ
  let hμ := hg.contDiffOn_density hKp
  let β := beta d.γ d.radius
  have hFloor' (x : X dim) (hx : x ∈ Y) : 1 ≤ β x := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  let H : CoordinateTraceFormContext hn Y := ⟨hY,μ,β,hμ,fun _ _ => Real.sqrt_nonneg _,
    fun x hx => zero_lt_one.trans_le (hFloor' x hx)⟩
  let B := H.Pairing
  have hD' (i : I dim) : PairedAdjoint B (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint hY i) :=
    actualCoordinatePrincipalTrace_baseAdjoint hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S V i
  have hA' (i j : I dim) : (U.second i j).reverse.action hY = (U.second j i).forward.action hY :=
    actualCoordinatePrincipalTrace_second_symm hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S V i j
  have ha' (i j : I dim) (F₀ : RegularTraceFiberFamily Y) :
      F₀.action hY*(U.second i j).forward.action hY = (U.second i j).forward.action hY*F₀.action hY :=
    actualCoordinatePrincipalTrace_scalar_comm hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S V i j F₀
  have hT' : PairedAdjoint B (T.action hY) (Td.action hY) :=
    CoordinateTraceFirstOrder.paired_ofPaired hY μ hμ U.density (P.model.first hY) (P.model.zero hY) hD'
  have hBd := bounded_coordinate_principalAdjointError H T Td (U.skew hY).neg U Z C (D*ε)
    hC (mul_nonneg hD hε) hFloor' hT' hD' hA' ha' (CoordinateTraceFirstOrder.neg_action hY _) hLocal
  let T₀ := physicalRaisingModel hY hg hKp he hlog hA hEll S
  let L₀ := physicalLoweringModel hY hg hKp he hlog hA hEll S
  let Z₀ := physicalTraceModelCorrection hY he hA hEll S hlog
  let Td₀ := L₀-Z₀
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let g := supportedReferenceTraceCoeff hY hg hKp hr
  let U₀ := movingTracePerturbation a (a-g) 0 (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S)
    (supportedCoordinateModelDerivative hY hg hKp he hlog hA hEll S)
    (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hCF hFF)
    (actualSupportedAffine hY F hFF)
  have hMatchU : U.action hY = U₀ :=
    actual_principalTrace_divergence_match hn hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S F hCF hFF V hV
  have hMatchT : T.action hY = T₀ :=
    actualCoordinateTraceModel_firstOrder hY hg hKp he hlog hA hEll S hFrame'
  have hMatchZ : Z.action hY = Z₀ := actualCoordinateTraceModel_correction hY hg hKp he hlog hA hEll S
  have hSymB : ∀ u w,B u w = B w u := smoothSupportedTracePairing_symm hn μ
  have hPairedT₀ : PairedAdjoint B T₀ Td₀ :=
    pairedAdjoint_physicalRaisingModel hY hg hKp he hFrame' hn hA hEll S hlog
  have hPairedU := U.paired hY μ hμ hD' hA'
  have hPairedU₀ : PairedAdjoint B U₀ (U.adjointAction hY) := hMatchU ▸ hPairedU
  have hPairedTd : PairedAdjoint B T₀ (Td.action hY) := hMatchT ▸ hT'
  have hForm (u : SmoothSupportedTraceSection Y) :
      movingTraceAdjointErrorForm B T₀ Td₀ L₀ U₀ Ud u =
        movingTraceAdjointErrorForm B (T.action hY) (Td.action hY) (Td.action hY+Z.action hY)
          (U.action hY) (U.adjointAction hY) u := by
    rw [movingTraceAdjointErrorForm_adj_congr T₀ Td₀ L₀ U₀ Ud _ hSymB hPairedT₀ hUd hPairedU₀ u]
    rw [movingTraceAdjointErrorForm_modelAdjoint_congr B T₀ Td₀ (Td.action hY) L₀ U₀ _
      u hSymB hPairedT₀ hPairedTd hPairedU₀]
    rw [hMatchU,hMatchT,hMatchZ,show L₀-Td₀ = Z₀ by dsimp only [Td₀]; abel]
  let e (x : X dim) := N*physicalEnergyDensity d.γ d.frame d.radius v x
  have he' : IntegrableOn e Y :=
    (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hn hY hg hKp d.frame he hFrame' hFloor hv).const_mul N
  let Mv := Classical.choice (exists_angularModelData hn hY hg hKp d.frame he hFrame' hv.1 Xv d.radius hlog)
  let u := Xv.traceComponent Complex.reCLM
  let w := Xv.traceComponent Complex.imCLM
  have hMajor (x : X dim) (hx : x ∈ Y) :
      μ x*(coordinateTraceEnergy hn β u x+coordinateTraceEnergy hn β w x) ≤ e x := by
    obtain ⟨_,_,hEntry,_,hΓ,_⟩ := hCoord floor hFloor ε hs₂ d hd hFrame x hx
    exact physical_coordinateTraceEnergy_le hn hY hg hKp he hFrame' hv Xv Mv hx (hFloor' x hx)
      E hE₀ (fun a i => hEntry i a) hΓ
  have hPos (v : SmoothSupportedTraceSection Y) (x : X dim) (hx : x ∈ Y) :
      0 ≤ coordinateTraceEnergy hn β v x := by
    have hβ := zero_le_one.trans (hFloor' x hx)
    unfold coordinateTraceEnergy
    positivity
  have hU (x : X dim) (hx : x ∈ Y) : μ x*coordinateTraceEnergy hn β u x ≤ e x :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hPos w x hx)) (Real.sqrt_nonneg _)).trans (hMajor x hx)
  have hW (x : X dim) (hx : x ∈ Y) : μ x*coordinateTraceEnergy hn β w x ≤ e x :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hPos u x hx)) (Real.sqrt_nonneg _)).trans (hMajor x hx)
  have hu := hBd u e he' hU
  have hw := hBd w e he' hW
  change |movingTraceAdjointErrorForm B T₀ Td₀ L₀ U₀ Ud u+movingTraceAdjointErrorForm B T₀ Td₀ L₀ U₀ Ud w| ≤ _
  rw [hForm u,hForm w]
  refine ((abs_add_le _ _).trans (add_le_add hu hw)).trans_eq ?_
  change Λ*(C*(D*ε))*(∫ x in Y,e x)+Λ*(C*(D*ε))*(∫ x in Y,e x) =
    C₀*ε*energySq Y d.γ d.frame d.radius v
  rw [energySq_eq_integral_density]
  simp only [e,integral_const_mul,C₀]
  ring

end CalderonN
