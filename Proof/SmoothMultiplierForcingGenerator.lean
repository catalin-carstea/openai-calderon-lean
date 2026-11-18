import Proof.BulkCoefficientMultiplierGenerator
import Proof.Archive.NativeSmoothMultiplierForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma nativeSmoothMultiplierForcing_zero_mass (C : I → SmoothCoefficientJets 2) (R : I → SmoothCoefficientJets 1) :
    nativeSmoothMultiplierForcingL fixedSobolevCalculus C R 0 =
    (∑ i : I,(unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL fixedSobolevCalculus (C i)))+
    (∑ j : I,(coefficientMultiplier fixedSobolevCalculus 0 (R j)).comp (unitBallCoordinateGradientL j)) := by
  have h0 : coefficientMultiplier fixedSobolevCalculus 0 (0:SmoothCoefficientJets 1) = 0 :=
    (coefficientMultiplierL fixedSobolevCalculus 0).map_zero
  simp only [nativeSmoothMultiplierForcingL,h0,ContinuousLinearMap.zero_comp,sub_zero]

/-- Actual common-support column and row forcing differentiates to the
same native forcing built from the actual compact parameter generators. -/
theorem hasDerivAt_commonSupport_smoothMultiplierForcing
    (C R : I → ℝ × X → ℝ) (hC : ∀ i,ContDiff ℝ ∞ (C i)) (hR : ∀ i,ContDiff ℝ ∞ (R i))
    (S : Set X) (hS : IsCompact S)
    (hzC : ∀ i t z,z ∉ S → C i (t,z) = 0) (hzR : ∀ i t z,z ∉ S → R i (t,z) = 0)
    (bC bR : I → X → ℝ) (hbC : ∀ i,ContDiff ℝ ∞ (bC i)) (hbR : ∀ i,ContDiff ℝ ∞ (bR i))
    (hzbC : ∀ i z,z ∉ S → bC i z = 0) (hzbR : ∀ i z,z ∉ S → bR i z = 0)
    (hSliceC : ∀ i z,HasDerivAt (fun t => C i (t,z)) (bC i z) 0)
    (hSliceR : ∀ i z,HasDerivAt (fun t => R i (t,z)) (bR i z) 0) :
    HasDerivAt (fun t => nativeSmoothMultiplierForcingL fixedSobolevCalculus
      (fun i => commonSupportCoefficientFamily 2 (C i) (hC i) S hS (hzC i) t)
      (fun i => commonSupportCoefficientFamily 1 (R i) (hR i) S hS (hzR i) t) 0)
      (nativeSmoothMultiplierForcingL fixedSobolevCalculus
        (fun i => compactCoefficient 2 (bC i) (hbC i) (HasCompactSupport.intro hS (hzbC i)))
        (fun i => compactCoefficient 1 (bR i) (hbR i) (HasCompactSupport.intro hS (hzbR i))) 0) 0 := by
  let CF := fun (t : ℝ) i => commonSupportCoefficientFamily 2 (C i) (hC i) S hS (hzC i) t
  let RF := fun (t : ℝ) i => commonSupportCoefficientFamily 1 (R i) (hR i) S hS (hzR i) t
  let CG := fun i => compactCoefficient 2 (bC i) (hbC i) (HasCompactSupport.intro hS (hzbC i))
  let RG := fun i => compactCoefficient 1 (bR i) (hbR i) (HasCompactSupport.intro hS (hzbR i))
  have hCol (i : I) : HasDerivAt
      (fun t => (unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL fixedSobolevCalculus (CF t i)))
      ((unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL fixedSobolevCalculus (CG i))) 0 := by
    have hM := hasDerivAt_commonSupport_bulkMultiplier_one (C i) (hC i) S hS (hzC i)
      (bC i) (hbC i) (hzbC i) (hSliceC i)
    let J : BallSobolev 1 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 0
    have hProd := (hasDerivAt_const (0:ℝ) J).clm_comp hM
    have hH1 : HasDerivAt (fun t => nativeCoefficientH1ProductL fixedSobolevCalculus (CF t i))
        (nativeCoefficientH1ProductL fixedSobolevCalculus (CG i)) 0 := by
      simpa only [nativeCoefficientH1ProductL,ContinuousLinearMap.zero_comp,zero_add,add_zero] using hProd
    have h := (hasDerivAt_const (0:ℝ) (unitBallCoordinateGradientL i)).clm_comp hH1
    simpa only [ContinuousLinearMap.zero_comp,zero_add,add_zero] using h
  have hRow (j : I) : HasDerivAt
      (fun t => (coefficientMultiplier fixedSobolevCalculus 0 (RF t j)).comp (unitBallCoordinateGradientL j))
      ((coefficientMultiplier fixedSobolevCalculus 0 (RG j)).comp (unitBallCoordinateGradientL j)) 0 := by
    have hM := hasDerivAt_commonSupport_bulkMultiplier_zero (R j) (hR j) S hS (hzR j)
      (bR j) (hbR j) (hzbR j) (hSliceR j)
    have h := hM.clm_comp (hasDerivAt_const (0:ℝ) (unitBallCoordinateGradientL j))
    simpa only [ContinuousLinearMap.comp_zero,zero_add,add_zero] using h
  have hSum := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hCol i)).add
    (HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hRow j))
  have hFun : (fun t => nativeSmoothMultiplierForcingL fixedSobolevCalculus (CF t) (RF t) 0) =
      (fun t => (∑ i : I,(unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL fixedSobolevCalculus (CF t i)))+
        (∑ j : I,(coefficientMultiplier fixedSobolevCalculus 0 (RF t j)).comp (unitBallCoordinateGradientL j))) :=
    funext (fun t => nativeSmoothMultiplierForcing_zero_mass (CF t) (RF t))
  change HasDerivAt (fun t => nativeSmoothMultiplierForcingL fixedSobolevCalculus (CF t) (RF t) 0)
    (nativeSmoothMultiplierForcingL fixedSobolevCalculus CG RG 0) 0
  rw [hFun,nativeSmoothMultiplierForcing_zero_mass]
  exact hSum

end ShrinkingSpheres
