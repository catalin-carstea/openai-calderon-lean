import Proof.ClosedLocalZeroMultiplier
import Proof.CommonSupportWeakEnergyRegularity
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

/-- Fixed finite forcing constants, independent of every coefficient cutoff. -/
def weakFullDerivativeBudget : ℝ := ∑ i : I,∑ j : I,
  ‖forcingFromValueL (unitBallCoordinateGradientL i)‖*‖unitBallCoordinateGradientL j‖

lemma weakFullDerivativeBudget_nonneg : 0 ≤ weakFullDerivativeBudget := by
  unfold weakFullDerivativeBudget
  positivity

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Native full weak energy derivatives depend only on the true local
    parameter derivative of the zeroth coefficient jet. -/
theorem norm_fderiv_commonSupportFullWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  let M := fun i j t => coefficientMultiplier fixedSobolevCalculus 0
    (commonSupportCoefficientFamily 1 (fun v => a v i j)
      (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl) t)
  let T := fun i j t => (forcingFromValueL (unitBallCoordinateGradientL i)).comp
    ((M i j t).comp (unitBallCoordinateGradientL j))
  have hMDiff (i j : I) : DifferentiableAt ℝ (M i j) p :=
    (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl)).differentiable (by simp) p
  have hTDiff (i j : I) : DifferentiableAt ℝ (T i j) p :=
    (differentiableAt_const (forcingFromValueL (unitBallCoordinateGradientL i))).clm_comp
      ((hMDiff i j).clm_comp (differentiableAt_const (unitBallCoordinateGradientL j)))
  have hMN (i j : I) : ‖fderiv ℝ (M i j) p‖ ≤ q :=
    norm_fderiv_commonSupport_coefficientMultiplier_zero_le fixedSobolevCalculus
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl) p q hq (hJet i j)
  have hTN (i j : I) : ‖fderiv ℝ (T i j) p‖ ≤
      (‖forcingFromValueL (unitBallCoordinateGradientL i)‖*‖unitBallCoordinateGradientL j‖)*q := by
    have hPre := norm_fderiv_clm_comp_le (M i j) (fun _ : P => unitBallCoordinateGradientL j) p
      (hMDiff i j) (differentiableAt_const _)
    have hPost := norm_fderiv_clm_comp_le
      (fun _ : P => forcingFromValueL (unitBallCoordinateGradientL i))
      (fun t => (M i j t).comp (unitBallCoordinateGradientL j)) p (differentiableAt_const _)
        ((hMDiff i j).clm_comp (differentiableAt_const _))
    simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero,zero_mul,zero_add] at hPre hPost
    have hInner : ‖fderiv ℝ (fun t => (M i j t).comp (unitBallCoordinateGradientL j)) p‖ ≤
        q*‖unitBallCoordinateGradientL j‖ :=
      hPre.trans (mul_le_mul_of_nonneg_right (hMN i j) (norm_nonneg _))
    exact hPost.trans ((mul_le_mul_of_nonneg_left hInner (norm_nonneg _)).trans_eq (by ring))
  have hEq : commonSupportFullWeakEnergy a ha = fun t => ∑ i : I,∑ j : I,T i j t := by
    funext t
    rw [← commonSupportFullWeakEnergy_smooth_eq a ha K hK hz]
    have hZero : coefficientMultiplier fixedSobolevCalculus 0 (0:SmoothCoefficientJets 1) = 0 :=
      (coefficientMultiplierL fixedSobolevCalculus 0).map_zero
    simp only [nativeSmoothCoefficientFullEnergyL,hZero,ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero,Finset.sum_const_zero,add_zero]
    rfl
  rw [hEq]
  have hD := HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hTDiff i j).hasFDerivAt))
  rw [hD.fderiv]
  calc
    _ ≤ ∑ i : I,‖∑ j : I,fderiv ℝ (T i j) p‖ := norm_sum_le _ _
    _ ≤ ∑ i : I,∑ j : I,‖fderiv ℝ (T i j) p‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : I,∑ j : I,(‖forcingFromValueL (unitBallCoordinateGradientL i)‖*
        ‖unitBallCoordinateGradientL j‖)*q := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTN i j))
    _ = _ := by simp only [weakFullDerivativeBudget,Finset.sum_mul]


end ShrinkingSpheres
