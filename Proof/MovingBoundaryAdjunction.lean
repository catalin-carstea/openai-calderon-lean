import Proof.CoarseValueAlgebra
import Proof.ConstantBoundaryCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The boundary action with the physical harmonic solution held fixed: the
    center gradient, radius derivative and true Jacobi center error. -/
def movingBoundaryHorizontalL (P C : I → SmoothCoefficientJets 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (r b : ℝ) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (r⁻¹ • boundaryGradientL P D+b • D)+r⁻¹ • boundaryGradientL C D

def movingBoundaryHorizontalAdjointL (P C : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (r b : ℝ) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (r⁻¹ • boundaryGradientAdjointL P Da+b • Da)+r⁻¹ • boundaryGradientAdjointL C Da

/-- Exact physical L2 adjunction for the assembled moving-boundary action. -/
theorem movingBoundaryHorizontalL_adjoint (P C : I → SmoothCoefficientJets 2)
    (D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (r b : ℝ)
    (hD : ∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ)
    (u v : SphereSobolev 1) :
    ⟪movingBoundaryHorizontalL P C D r b u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,movingBoundaryHorizontalAdjointL P C Da r b v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  change ⟪(r⁻¹ • boundaryGradientL P D u+b • D u)+r⁻¹ • boundaryGradientL C D u,I0 v⟫_ℝ =
    ⟪I0 u,(r⁻¹ • boundaryGradientAdjointL P Da v+b • Da v)+r⁻¹ • boundaryGradientAdjointL C Da v⟫_ℝ
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right]
  rw [boundaryGradientL_adjoint P D Da hD u v,hD u v,boundaryGradientL_adjoint C D Da hD u v]

/-- The assembled forward operator is the actual horizontal derivative of the
    trace of the fixed physical harmonic solution. -/
theorem Admissible.movingBoundaryHorizontalL_value_ae {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (a : X) (P C : I → SmoothCoefficientJets 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (f : SphereSobolev 1)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (hP : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (boundaryGradientL P D f)
      =ᵐ[sphereProbability] fun w : UnitSphere =>
        fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val) a)
    (hRadial : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (D f)
      =ᵐ[sphereProbability] fun w : UnitSphere => radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u)
    (hC : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (boundaryGradientL C D f)
      =ᵐ[sphereProbability] fun w : UnitSphere =>
        fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val)
          ((normalizedParallelCenterJacobian d.γ d.expMap y
            (d.radius y • frameVector d.frame y w.val)-ContinuousLinearMap.id ℝ X) a)) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (movingBoundaryHorizontalL P C D (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) f)
        =ᵐ[sphereProbability] fun w : UnitSphere =>
          horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y (frameVector d.frame y w.val) a := by
  let b := fderiv ℝ (fun x => Real.log (d.radius x)) y a
  have h1 := coarseValue_smul (d.radius y)⁻¹ _ _ hP
  have h2 := coarseValue_smul b _ _ hRadial
  have h3 := coarseValue_smul (d.radius y)⁻¹ _ _ hC
  have hSum := coarseValue_add _ _ _ _ (coarseValue_add _ _ _ _ h1 h2) h3
  change (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
    (((d.radius y)⁻¹ • boundaryGradientL P D f+b • D f)+(d.radius y)⁻¹ • boundaryGradientL C D f) =ᵐ[sphereProbability] _
  filter_upwards [hSum] with w hw
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  exact hw.trans (hd.horizontal_normal_pullback_decomposition hY hy
    (frameVector_mem_sphere d.γ d.frame y hFrame w) a u hu).symm

end ShrinkingSpheres
