import Proof.EffectiveFirstAdjointFiveHalfMeasurability
import Proof.CovariantHalfOperatorGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalFirstCommutatorPacket.covariantAdjointLowSection
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) :
    SphereSobolev (1/2:ℝ) :=
  WF.covariantCoordinateAdjointHigher b y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))

/-- Density-weighted fibre L2 expression for the negative of a first
formal-adjoint row. Only the smooth LOW section is differentiated. -/
def PhysicalPrincipalData.firstAdjointDensityCoreRow
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev (1/2:ℝ) :=
  metricDensity d.γ y • fderiv ℝ (WF.covariantAdjointLowSection U b) y (axis b)-
    metricDensity d.γ y • frameAngularConnectionHigherL d y (axis b)
      (P.firstCovariantAdjointFiveHalfSection WQ U b y)+
    fderiv ℝ (metricDensity d.γ) y (axis b) • WF.covariantAdjointLowSection U b y

def PhysicalPrincipalData.firstAdjointWeakDensityRow
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev (-(1/2:ℝ)) :=
  let V := fun x => (P.firstCovariantCoordinateHalfL b x).adjoint
    (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
  metricDensity d.γ y • fderiv ℝ V y (axis b)-
    metricDensity d.γ y • frameAngularConnectionHalfL d y (axis b) (WF.covariantAdjointLowSection U b y)+
    fderiv ℝ (metricDensity d.γ) y (axis b) • V y

/-- Actual weak graph of the density core. No derivative or smoothness of
the pointwise selected HIGH lift is assumed. -/
lemma PhysicalPrincipalData.firstAdjointDensityCoreRow_graph
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (P.firstAdjointDensityCoreRow WF WQ U b y)=P.firstAdjointWeakDensityRow WF U b y := by
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Z := WF.covariantAdjointLowSection U b
  let V := fun x => (P.firstCovariantCoordinateHalfL b x).adjoint
    (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
  have hZ : ContDiffOn ℝ ∞ Z Y := (WF.covariantCoordinateAdjointHigher_smooth hd b hw).clm_apply
    ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn hU)
  have hObs (x : X) (hx : x ∈ Y) : T (Z x)=V x := by
    have hh := DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hx)
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x))
    simpa only [Z,V,T,PhysicalFirstCommutatorPacket.covariantAdjointLowSection,
      ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh
  have hNear : (fun x => T (Z x)) =ᶠ[𝓝 y] V := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hObs x hx
  have hZD := ((hZ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hDer := (T.hasFDerivAt.comp y hZD).congr_of_eventuallyEq hNear.symm
  have hFD : fderiv ℝ V y (axis b)=T (fderiv ℝ Z y (axis b)) :=
    DFunLike.congr_fun hDer.fderiv (axis b)
  have hTop := DFunLike.congr_fun (P.firstCovariantCoordinateAdjointFiveHalfL_inclusion hy (WQ y hy) b
    (WF.covariantCoordinateAdjointHigher b y) (WF.covariantCoordinateAdjointHigher_balanced b hy)) (U y)
  have hTop' : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (P.firstCovariantAdjointFiveHalfSection WQ U b y)=Z y := by
    simpa only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dite_eq_left hy,
      Z,PhysicalFirstCommutatorPacket.covariantAdjointLowSection,ContinuousLinearMap.comp_apply] using hTop
  have hR := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y (axis b))
    (P.firstCovariantAdjointFiveHalfSection WQ U b y)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hTop'] at hR
  have hR' : T (frameAngularConnectionHigherL d y (axis b)
      (P.firstCovariantAdjointFiveHalfSection WQ U b y))=
      frameAngularConnectionHalfL d y (axis b) (Z y) := hR
  change T (metricDensity d.γ y • fderiv ℝ Z y (axis b)-
    metricDensity d.γ y • frameAngularConnectionHigherL d y (axis b)
      (P.firstCovariantAdjointFiveHalfSection WQ U b y)+
    fderiv ℝ (metricDensity d.γ) y (axis b) • Z y)=_
  simp only [map_add,map_sub,map_smul,hR',←hFD,hObs y hy]
  rfl

lemma PhysicalPrincipalData.firstAdjointDensityCoreRow_aestronglyMeasurable
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    AEStronglyMeasurable (P.firstAdjointDensityCoreRow WF WQ U b) (volume.restrict Y) := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hZ : ContDiffOn ℝ ∞ (WF.covariantAdjointLowSection U b) Y :=
    (WF.covariantCoordinateAdjointHigher_smooth hd b hw).clm_apply
      ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn hU)
  have hDZ := (hZ.fderiv_of_isOpen hY (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => axis b) Y)
  have hMu := hg.contDiffOn_density hK
  have hDMu := (hMu.fderiv_of_isOpen hY (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => axis b) Y)
  have hHigh := P.firstCovariantAdjointFiveHalfSection_aestronglyMeasurable hY hd WF WQ U hU b hw
  have hR := (contDiffOn_frameAngularConnectionHigherL hY d hg hK he (axis b)).continuousOn.aestronglyMeasurable
    (μ:=volume) hY.measurableSet
  have hMuM := hMu.continuousOn.aestronglyMeasurable (μ:=volume) hY.measurableSet
  have hEval : Continuous (fun p :
      (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) × SphereSobolev (3/2:ℝ) => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hRHigh := hEval.comp_aestronglyMeasurable (hR.prodMk hHigh)
  exact ((hMuM.smul (hDZ.continuousOn.aestronglyMeasurable hY.measurableSet)).sub
    (hMuM.smul hRHigh)).add
      ((hDMu.continuousOn.aestronglyMeasurable hY.measurableSet).smul
        (hZ.continuousOn.aestronglyMeasurable hY.measurableSet))

end ShrinkingSpheres
