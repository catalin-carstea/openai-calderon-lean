import Proof.NativeMultiplierForcingMultiplierLinearity
import Proof.CoefficientMultiplierTwoJetBound
import Proof.NativeMultiplierFirstVariationScaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- The genuine native forcing has a product norm bound in the matrix and
multiplier jet spaces, using the supplied coordinate Sobolev calculus. -/
theorem norm_nativeBulkMultiplierForcing_matrix_multiplier_le
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) :
    ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖ ≤
      (15*nativeMultiplierForcingGradientBudget)*‖F‖*‖Q‖ := by
  have hEntry (i j : I) : ‖F i j‖ ≤ ‖F‖ :=
    (norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i)
  have hF0 (i j : I) (z : X) (_hz : z ∈ (ballOpens:Set X)) : |coefficientValue 2 (F i j) z| ≤ ‖F‖ := by
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 0 (by omega) z
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h.trans (hEntry i j)
  have hF1 (i j : I) (z : X) (_hz : z ∈ (ballOpens:Set X)) : ‖gradient (coefficientValue 2 (F i j)) z‖ ≤ ‖F‖ := by
    rw [TauCeti.norm_gradient_eq_norm_fderiv]
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 1 (by omega) z
    simpa only [norm_iteratedFDeriv_one] using h.trans (hEntry i j)
  obtain ⟨hQ1,hQ2⟩ := coefficient_multiplier_two_jet_bound Q
  exact (norm_nativeBulkMultiplierForcing_local_C1 F Q ‖F‖ ‖Q‖ (norm_nonneg _) (norm_nonneg _)
    hF0 hF1 (fun j z _ => hQ1 j z) (fun j z _ => hQ2 j z)).trans_eq (by ring)

def nativeBulkMultiplierForcingInMultiplierLinear (F : SmoothCoefficientMatrix 2) :
    SmoothCoefficientJets 3 →ₗ[ℝ] (BallH1 →L[ℝ] BallSobolev 0) where
  toFun Q := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q
  map_add' Q R := nativeBulkMultiplierForcing_multiplier_add fixedSobolevCalculus F Q R
  map_smul' c Q := nativeBulkMultiplierForcing_multiplier_smul fixedSobolevCalculus F Q c

def nativeBulkMultiplierForcingInMultiplierL (F : SmoothCoefficientMatrix 2) :
    SmoothCoefficientJets 3 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0) :=
  (nativeBulkMultiplierForcingInMultiplierLinear F).mkContinuous
    ((15*nativeMultiplierForcingGradientBudget)*‖F‖)
    (fun Q => norm_nativeBulkMultiplierForcing_matrix_multiplier_le F Q)

lemma nativeBulkMultiplierForcing_coefficient_add (F G : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) :
    nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F+G) (fun _ => 0) Q =
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q+
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus G (fun _ => 0) Q := by
  have h := nativeBulkMultiplierForcing_affine_on_ball fixedSobolevCalculus (F+G) F G Q 1 (by
    intro z hz i j
    change coefficientValue 2 (F i j+G i j) z = _
    simp only [coefficientValue_add,Pi.add_apply,one_mul])
  simpa only [one_smul] using h

def nativeBulkMultiplierForcingBilinear : SmoothCoefficientMatrix 2 →ₗ[ℝ]
    SmoothCoefficientJets 3 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0) where
  toFun := nativeBulkMultiplierForcingInMultiplierL
  map_add' F G := by
    apply ContinuousLinearMap.ext
    intro Q
    exact nativeBulkMultiplierForcing_coefficient_add F G Q
  map_smul' c F := by
    apply ContinuousLinearMap.ext
    intro Q
    exact nativeBulkMultiplierForcing_coefficient_smul F c Q

def nativeBulkMultiplierForcingBilinearL : SmoothCoefficientMatrix 2 →L[ℝ]
    SmoothCoefficientJets 3 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0) :=
  nativeBulkMultiplierForcingBilinear.mkContinuous (15*nativeMultiplierForcingGradientBudget) (by
    intro F
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num) nativeMultiplierForcingGradientBudget_nonneg) (norm_nonneg F))
    intro Q
    exact norm_nativeBulkMultiplierForcing_matrix_multiplier_le F Q)

end ShrinkingSpheres
