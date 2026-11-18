import Proof.PhysicalCoordinateTrace
import Proof.UniformCenterBoundaryAdjoint
import Proof.NormalCenterBoundaryChainRule

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

theorem weightedCoordinateTrace_value_ae (C : I → SmoothCoefficientJets 2)
    (v : I → SphereL2) (b : I → UnitSphere → ℝ)
    (hValue : ∀ j,v j =ᵐ[sphereProbability] b j) :
    (∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (C j))) (v j))
      =ᵐ[sphereProbability] fun w : UnitSphere => ∑ j : I,coefficientValue 2 (C j) w.val*b j w := by
  have hProduct : ∀ᵐ w ∂sphereProbability,∀ j : I,
      sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (C j))) (v j) w =
        smoothSphereValue (coefficientSmoothData (C j)) w*v j w :=
    ae_all_iff.mpr (fun j => sphereContinuousScalarMul_value_ae _ _)
  have hValues := ae_all_iff.mpr hValue
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : I => sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (C j))) (v j)),
    hProduct,hValues] with w hSum hMul hVal
  rw [hSum]
  apply Finset.sum_congr rfl
  intro j _
  exact (hMul j).trans (congrArg (fun t : ℝ => coefficientValue 2 (C j) w.val*t) (hVal j))

/-- Actual pointwise boundary values of the completed coefficient-gradient map. -/
theorem boundaryGradientL_value_ae (C : I → SmoothCoefficientJets 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (U : BallSobolev 2) (u : SphereSobolev 1)
    (hTrace : OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
        (TauCeti.Wkp.firstOrder 1 U) = sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
    (hRadial : D u = sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U))
    (b : I → UnitSphere → ℝ)
    (hCoordinate : ∀ j,strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U
      =ᵐ[sphereProbability] b j) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (boundaryGradientL C D u)
      =ᵐ[sphereProbability] fun w : UnitSphere => ∑ j : I,coefficientValue 2 (C j) w.val*b j w := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hEq := congrArg Z.symm (boundaryGradientL_nativeH2 C D U u hTrace hRadial)
  have hLpEq : Z.symm (boundaryGradientL C D u) =
      ∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (C j)))
        (strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U) :=
    hEq.trans (Z.symm_apply_apply _)
  exact hLpEq.symm ▸ weightedCoordinateTrace_value_ae C _ b hCoordinate

lemma normalChart_coordinate_derivative (expMap : X × X → X) (e : Frame) (r u : X → ℝ)
    (y z : X) (j : I) (hB : DifferentiableAt ℝ (ballPullback expMap r y u) (frameVector e y z)) :
    fderiv ℝ (u ∘ normalChart expMap e y (r y)) z (axis j) =
      fderiv ℝ (ballPullback expMap r y u) (frameVector e y z) (e y j) := by
  have h := hB.hasFDerivAt.comp z (frameVectorLinear e y).hasFDerivAt
  have hEval := congrArg (fun L : X →L[ℝ] ℝ => L (axis j)) h.fderiv
  simpa only [Function.comp_def,frameVectorLinear_apply,ContinuousLinearMap.comp_apply,
    frameVector_axis,ballPullback,normalChart] using hEval

/-- Exact physical reconstruction of an ambient gradient from frame-coordinate
    derivatives. The harmonic solution is held fixed throughout the derivative. -/
theorem Admissible.frame_gradient_eq {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (b : X) (z : UnitSphere) (c : I → ℝ)
    (hReconstruct : (∑ j : I,c j • d.frame y j) = b) :
    (∑ j : I,c j*fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) z.val (axis j)) =
      fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y z.val) b := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hwSphere := frameVector_mem_sphere d.γ d.frame y hFrame z
  obtain ⟨hRadius,hExp,hU⟩ := dirichlet_differentiability Y Ω hY hd y _ hy hwSphere u hu
  have hScale := (hasFDerivAt_const (𝕜:=ℝ) y (frameVector d.frame y z.val)).prodMk
    ((hasFDerivAt_id (𝕜:=ℝ) (frameVector d.frame y z.val)).const_smul (d.radius y))
  have hB : DifferentiableAt ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y z.val) :=
    (hU.hasFDerivAt.comp (frameVector d.frame y z.val)
      (hExp.hasFDerivAt.comp (frameVector d.frame y z.val) hScale)).differentiableAt
  simp_rw [normalChart_coordinate_derivative d.expMap d.frame d.radius u y z.val _ hB]
  have hMap := map_sum (fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y z.val))
    (fun j : I => c j • d.frame y j) Finset.univ
  rw [hReconstruct] at hMap
  simpa only [map_smul,smul_eq_mul] using hMap.symm

/-- The frame-coordinate coefficients reconstruct the actual Jacobi center
    error in the boundary gradient action. -/
theorem Admissible.center_error_gradient_eq {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (a : X) (z : UnitSphere) (c : I → ℝ)
    (hReconstruct : (∑ j : I,c j • d.frame y j) =
      (normalizedParallelCenterJacobian d.γ d.expMap y
        (d.radius y • frameVector d.frame y z.val)-ContinuousLinearMap.id ℝ X) a) :
    (∑ j : I,c j*fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) z.val (axis j)) =
      fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y z.val)
        ((normalizedParallelCenterJacobian d.γ d.expMap y
          (d.radius y • frameVector d.frame y z.val)-ContinuousLinearMap.id ℝ X) a) :=
  hd.frame_gradient_eq hY hy u hu _ z c hReconstruct

end ShrinkingSpheres
