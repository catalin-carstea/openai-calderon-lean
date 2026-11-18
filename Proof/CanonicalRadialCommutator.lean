import Proof.RadialCorrectionFrameCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def firstRadialHorizontalCommutatorL (d : Data) (y a : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (fderiv ℝ (firstRadialCorrectionL d) y a).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
    ((angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp
      (radialCorrectionSobolevL 1 (firstDensityLogCovector d y))-
        (firstRadialCorrectionL d y).comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)))

def firstRadialAdjointHorizontalCommutatorL (d : Data) (y a : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (fderiv ℝ (fun x => (firstRadialCorrectionL d x).adjoint) y a).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
    ((angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp
      (radialCorrectionAdjointSobolevL 1 (firstDensityLogCovector d y))-
        (firstRadialCorrectionL d y).adjoint.comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)))

theorem Background.firstRadialHorizontalCommutatorL_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    firstRadialHorizontalCommutatorL d y a =
      (firstRadialCoefficientCovariantJetL d y a).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let A := frameConnectionCoefficient d.γ d.frame y a
  let q := firstDensityLogCovector d y
  let L := angularConnectionL A
  have hA : ∀ i j,A i j = -A j i :=
    frameConnection_skew hΩ hB.1 hK d.frame hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2 hy a
  have hComm := angularConnection_radialCorrection_commutator A hA q
  have hActual : L.comp (radialCorrectionSobolevL 1 q)-(firstRadialCorrectionL d y).comp L =
      (radialCorrectionCovectorL (firstDensityFrameActionL d y a)).comp I0 :=
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
      L.comp (radialCorrectionSobolevL 1 q)-T.comp L) (firstRadialCorrectionL_eq_covector d y)).trans hComm
  have hFirst := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    (fderiv ℝ (firstRadialCorrectionL d) y a).comp I0+T) hActual
  have hSum := (ContinuousLinearMap.add_comp (fderiv ℝ (firstRadialCorrectionL d) y a)
    (radialCorrectionCovectorL (firstDensityFrameActionL d y a)) I0).symm
  exact hFirst.trans (hSum.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.comp I0)
    (hB.firstRadialCorrectionL_covariant_derivative hΩ hK hy a)))

theorem Background.fderiv_firstRadialCorrectionL_adjoint {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    fderiv ℝ (fun x => (firstRadialCorrectionL d x).adjoint) y a =
      (fderiv ℝ (firstRadialCorrectionL d) y a).adjoint := by
  let J : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hF := ((hB.firstRadialCorrectionL_smooth hΩ hK).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hD := congrArg (fun T : X →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) => T a)
    (J.hasFDerivAt.comp y hF.hasFDerivAt).fderiv
  exact hD

theorem Background.firstRadialAdjointHorizontalCommutatorL_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    firstRadialAdjointHorizontalCommutatorL d y a =
      (firstRadialCoefficientCovariantJetL d y a).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let A := frameConnectionCoefficient d.γ d.frame y a
  let q := firstDensityLogCovector d y
  let L := angularConnectionL A
  have hA : ∀ i j,A i j = -A j i :=
    frameConnection_skew hΩ hB.1 hK d.frame hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2 hy a
  have hComm := angularConnection_radialCorrectionAdjoint_commutator A hA q
  have hActual : L.comp (radialCorrectionAdjointSobolevL 1 q)-(firstRadialCorrectionL d y).adjoint.comp L =
      (radialCorrectionCovectorL (firstDensityFrameActionL d y a)).adjoint.comp I0 :=
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
      L.comp (radialCorrectionAdjointSobolevL 1 q)-T.adjoint.comp L) (firstRadialCorrectionL_eq_covector d y)).trans hComm
  have hDerivative := hB.fderiv_firstRadialCorrectionL_adjoint hΩ hK hy a
  have hFirst := congrArg₂ (fun D : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
      fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => D.comp I0+T) hDerivative hActual
  have hCov := congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.adjoint)
    (hB.firstRadialCorrectionL_covariant_derivative hΩ hK hy a)
  have hCov' : (fderiv ℝ (firstRadialCorrectionL d) y a).adjoint+
      (radialCorrectionCovectorL (firstDensityFrameActionL d y a)).adjoint =
        (firstRadialCoefficientCovariantJetL d y a).adjoint := by simpa only [map_add] using hCov
  exact hFirst.trans ((ContinuousLinearMap.add_comp _ _ I0).symm.trans
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.comp I0) hCov'))

/-- A shared bounded L2 producer for the actual forward and adjoint covariant
    horizontal commutators, uniform over arbitrary smooth orthonormal frames. -/
theorem Background.exists_bounded_firstRadialHorizontalCommutator {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X) :
    ∃ J : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
      ‖J‖ ≤ 6*K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
        (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))*‖a‖ ∧
      firstRadialHorizontalCommutatorL d y a = J.comp (sphereSobolevInclusionL 1 0 (by norm_num)) ∧
      firstRadialAdjointHorizontalCommutatorL d y a = J.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
  ⟨firstRadialCoefficientCovariantJetL d y a,hB.norm_firstRadialCoefficientCovariantJetL_le hΩ hK hm hy a,
    hB.firstRadialHorizontalCommutatorL_eq hΩ (zero_lt_one.trans_le hK) hy a,
    hB.firstRadialAdjointHorizontalCommutatorL_eq hΩ (zero_lt_one.trans_le hK) hy a⟩

end ShrinkingSpheres
