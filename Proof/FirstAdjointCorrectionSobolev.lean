import Proof.ScaledFrameLogRadiusSmall
import Proof.FirstAdjointCorrectionGraded
import Proof.CoordinateMultiplierSobolev
import Proof.RadialCorrectionDegreeCommutator
import Proof.CanonicalFirstRadialCorrection
import Proof.ScaledLogRadiusBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem firstBoundaryAdjointCorrectionL_eq_sobolev_zero (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (q : X →L[ℝ] ℝ) (r b : ℝ) (i : I) :
    firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i) (radialCorrectionCovectorL q) r b =
      firstAdjointCorrectionSobolevL 0 q (r*b) i := by
  simp only [firstBoundaryAdjointCorrectionL,firstAdjointCorrectionSobolevL,
    radialCorrectionAdjointSobolevL_zero,coordinateMultiplierSobolevL_zero,coordinate_normal_value Q hQ i]

theorem firstAdjointCorrectionSobolevL_coarse (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (firstAdjointCorrectionSobolevL 1 q t i u) =
      firstAdjointCorrectionSobolevL 0 q t i (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  exact firstAdjointCorrectionSobolevL_inclusion 1 0 (by norm_num) q t i u

theorem norm_firstAdjointCorrectionSobolevL_one_le (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    ‖firstAdjointCorrectionSobolevL 1 q t i‖ ≤ 12*‖q‖*(6+|t|) := by
  have h := norm_firstAdjointCorrectionSobolevL_le 1 q t i
  have hOne : radialDriftSobolevBound 1 = 1 := by norm_num [radialDriftSobolevBound]
  have hNeg : radialDriftSobolevBound (-1) = 2 := by norm_num [radialDriftSobolevBound]
  rw [hOne,hNeg] at h
  exact h.trans_eq (by ring)

theorem norm_firstAdjointCorrectionSobolevL_zero_le (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    ‖firstAdjointCorrectionSobolevL 0 q t i‖ ≤ 6*‖q‖*(1+|t|) := by
  have hB : ‖radialCorrectionAdjointSobolevL 0 q‖ ≤ 6*‖q‖ := by
    rw [radialCorrectionAdjointSobolevL_zero,ContinuousLinearMap.adjoint.norm_map]
    exact norm_radialCorrectionCovectorL_apply_le q
  have hM := norm_coordinateMultiplierSobolevL_zero_le i
  calc
    _ ≤ ‖(radialCorrectionAdjointSobolevL 0 q).comp (coordinateMultiplierSobolevL 0 i)‖+
        ‖t • radialCorrectionAdjointSobolevL 0 q‖ := norm_add_le _ _
    _ ≤ ‖radialCorrectionAdjointSobolevL 0 q‖*‖coordinateMultiplierSobolevL 0 i‖+
        |t| *‖radialCorrectionAdjointSobolevL 0 q‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl
    _ ≤ (6*‖q‖)*1+|t| *(6*‖q‖) := by gcongr
    _ = _ := by ring

theorem Admissible.scaled_frame_logRadius_bound {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i : I) :
    |d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)| ≤ 1 := by
  exact (hd.scaled_frame_logRadius_small hf hy i).trans ((div_le_self hε hf).trans hε1)

def firstFrameAdjointCorrectionSobolevL (d : Data) (y : X) (i : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  firstAdjointCorrectionSobolevL 1 (firstDensityLogCovector d y)
    (d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) i

theorem firstFrameAdjointCorrectionSobolevL_coarse (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X) (i : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (firstFrameAdjointCorrectionSobolevL d y i u) =
      firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i) (firstRadialCorrectionL d y)
        (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i))
          (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have hEq := firstBoundaryAdjointCorrectionL_eq_sobolev_zero Q hQ (firstDensityLogCovector d y)
    (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) i
  have hActual := congrArg (fun B : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i) B (d.radius y)
      (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i))) (firstRadialCorrectionL_eq_covector d y)
  have hFinal := hActual.trans hEq
  exact (firstAdjointCorrectionSobolevL_coarse _ _ i u).trans
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
      T (sphereSobolevInclusionL 1 0 (by norm_num) u)) hFinal).symm

theorem Admissible.norm_firstFrameAdjointCorrectionSobolevL_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i : I) :
    ‖firstFrameAdjointCorrectionSobolevL d y i‖ ≤ 84*K^2*|M ⟨1,by omega⟩| := by
  have hQ := hd.1.norm_firstDensityLogCovector_le hΩ hK hm (hd.2.1.center_mem hy)
  have hT := hd.scaled_frame_logRadius_bound hf hε hε1 hy i
  calc
    _ ≤ 12*‖firstDensityLogCovector d y‖*
        (6+|d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)|) :=
      norm_firstAdjointCorrectionSobolevL_one_le _ _ i
    _ ≤ 12*(K^2*|M ⟨1,by omega⟩|)*(6+1) := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
