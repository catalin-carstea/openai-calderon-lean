import Proof.CanonicalFirstRadialCovariantJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem contDiffOn_frameVectorLinear {Ω : Set X} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Ω) :
    ContDiffOn ℝ ∞ (frameVectorLinear e) Ω := by
  apply ContDiffOn.sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ X X) (EuclideanSpace.proj (𝕜:=ℝ) i)).contDiff.comp_contDiffOn (he i)

theorem Background.firstDensityLogCovector_smooth {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstDensityLogCovector d) Ω := by
  have hT := (hB.firstMetricConformalDepth_smooth hK).fderiv_of_isOpen (m:=∞) hΩ (by simp)
  have hE := contDiffOn_frameVectorLinear d.frame hB.2.2.2.2.2.2.1
  apply (hT.clm_comp hE).neg.congr
  intro x hx
  exact hB.firstDensityLogCovector_eq_depth hΩ hK hx

theorem Background.firstRadialCorrectionL_smooth {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstRadialCorrectionL d) Ω := by
  have hEq : firstRadialCorrectionL d = (fun x => radialCorrectionCovectorL (firstDensityLogCovector d x)) :=
    funext (firstRadialCorrectionL_eq_covector d)
  rw [hEq]
  exact radialCorrectionCovectorL.contDiff.comp_contDiffOn (hB.firstDensityLogCovector_smooth hΩ hK)

theorem Background.fderiv_firstRadialCorrectionL {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    fderiv ℝ (firstRadialCorrectionL d) y a =
      radialCorrectionCovectorL (fderiv ℝ (firstDensityLogCovector d) y a) := by
  have hq := ((hB.firstDensityLogCovector_smooth hΩ hK).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hEq : firstRadialCorrectionL d = (fun x => radialCorrectionCovectorL (firstDensityLogCovector d x)) :=
    funext (firstRadialCorrectionL_eq_covector d)
  rw [hEq,(hasFDerivAt_radialCorrectionCovector hq.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply]

def frameAngularLinear (A : I → I → ℝ) : X →L[ℝ] X :=
  ∑ i : I,∑ j : I,(-A i j) • (EuclideanSpace.proj (𝕜:=ℝ) i).smulRight (axis j)

theorem frameAngularLinear_apply (A : I → I → ℝ) (z : X) :
    frameAngularLinear A z = frameAngularVector A z := by
  simp only [frameAngularLinear,frameAngularVector,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul]

def firstDensityFrameActionL (d : Data) (y a : X) : X →L[ℝ] ℝ :=
  (firstDensityLogCovector d y).comp (frameAngularLinear (frameConnectionCoefficient d.γ d.frame y a))

theorem Background.firstDensityCovariantDerivativeL_actual {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    firstDensityCovariantDerivativeL d y a =
      fderiv ℝ (firstDensityLogCovector d) y a+firstDensityFrameActionL d y a := by
  have hq := ((hB.firstDensityLogCovector_smooth hΩ hK).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hScalar (i : I) : fderiv ℝ (fun x => firstDensityLogCovector d x (axis i)) y a =
      fderiv ℝ (firstDensityLogCovector d) y a (axis i) := by
    have h := congrArg (fun T : X →L[ℝ] ℝ => T a)
      (hq.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜:=ℝ) (axis i) y)).fderiv
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,add_zero,zero_add] using h
  apply ContinuousLinearMap.ext
  intro z
  rw [← axis_expansion z]
  simp only [map_sum,map_smul,_root_.add_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun t : ℝ => (z i) • t)
  simp only [firstDensityCovariantDerivativeL,_root_.sum_apply,_root_.smul_apply,
    PiLp.proj_apply,smul_eq_mul,axis,PiLp.single_apply]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hHere := hScalar i
  dsimp only [axis] at hHere
  rw [hHere,firstDensityFrameActionL,ContinuousLinearMap.comp_apply,frameAngularLinear_apply]

/-- The actual operator-family derivative plus its explicit frame action is
    controlled by the covariant coefficient jet. Rotation covariance is the
    remaining step to express the frame action as an angular commutator. -/
theorem Background.firstRadialCorrectionL_covariant_derivative {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    fderiv ℝ (firstRadialCorrectionL d) y a+radialCorrectionCovectorL (firstDensityFrameActionL d y a) =
      firstRadialCoefficientCovariantJetL d y a := by
  rw [hB.fderiv_firstRadialCorrectionL hΩ hK hy,firstRadialCoefficientCovariantJetL,
    hB.firstDensityCovariantDerivativeL_actual hΩ hK hy,map_add]

/-- Uniform norm bound for the actual corrected operator-family derivative.
    No derivative of the arbitrary orthonormal frame enters the constant. -/
theorem Background.norm_firstRadialCorrectionL_covariant_derivative_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X) :
    ‖fderiv ℝ (firstRadialCorrectionL d) y a+radialCorrectionCovectorL (firstDensityFrameActionL d y a)‖ ≤
      6*K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
        (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))*‖a‖ := by
  rw [hB.firstRadialCorrectionL_covariant_derivative hΩ (zero_lt_one.trans_le hK) hy]
  exact hB.norm_firstRadialCoefficientCovariantJetL_le hΩ hK hm hy a

end ShrinkingSpheres
