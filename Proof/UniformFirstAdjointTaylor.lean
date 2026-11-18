import Proof.FirstAdjointNormalForm
import Proof.ScaledLogRadiusBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual frozen first adjoint equals its model plus a uniformly bounded
    L2 correction and a radius-small H1-to-L2 remainder, for arbitrary admitted
    profiles. This statement does not assert parameter derivative bounds. -/
theorem uniform_frozen_first_adjoint_taylor_canonical {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CQ CR : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CB ∧ 0 ≤ CQ ∧ 0 ≤ CR ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,B = firstRadialCorrectionL d y ∧ ‖B‖ ≤ CB ∧
        ∀ i : I,∃ J : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ‖firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) B
            (d.radius y) (coordDeriv i (fun x => Real.log (d.radius x)) y)‖ ≤ CQ ∧
          ‖J‖ ≤ CR*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (modelBoundaryAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) (d.radius y)
                (coordDeriv i (fun x => Real.log (d.radius x)) y) v+
              firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) B (d.radius y)
                (coordDeriv i (fun x => Real.log (d.radius x)) y)
                  (sphereSobolevInclusionL 1 0 (by norm_num) v)+J v) =ᵐ[sphereProbability]
                    fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  have hTheorem := uniform_frozen_trace_adjoint_realization_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CD,CB,CJ,CE,Q,hηA,hCD,hCB,hCJ,hCE,hQ,hActual⟩ := hTheorem
  let CC := 9*|M 0| *K
  let CQ := CB*(6*CC+K)
  let CR := CJ*(438*CC)+K*CJ+CE
  have hCC : 0 ≤ CC := by dsimp only [CC];positivity
  have hCQ : 0 ≤ CQ := by dsimp only [CQ];positivity
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  refine ⟨min ηA 1,CB,CQ,CR,Q,lt_min hηA zero_lt_one,hCB,hCQ,hCR,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hActual floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨Da,B,hDa,hCanonical,hB,hTaylor,hDirection⟩ := hHere
  refine ⟨B,hCanonical,hB,?_⟩
  intro i
  have hIHere := hDirection i
  obtain ⟨C,hCRep,hCenter,hReal⟩ := hIHere
  let P := fixedCenterCoefficient Q d.γ d.frame y (axis i)
  let r := d.radius y
  let b := coordDeriv i (fun x => Real.log (d.radius x)) y
  let J := firstBoundaryAdjointRemainderL P C Da B r b
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hNorms := hd.fixedCenter_normal_multiplier_norms hK hy Q hQ (axis i)
  simp only [norm_axis,mul_one] at hNorms
  have hNormalOne : ‖oneBoundaryCoefficientMulL (vectorNormalJet P)‖ ≤ 438*CC := hNorms.1
  have hNormalZero : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet P)))‖ ≤ 6*CC := hNorms.2
  have hBeta : r*|b| ≤ K := hd.scaled_coord_logRadius_bound hK hf hε (hSmall.trans (min_le_right _ _)) hy i
  have hCorrection : ‖firstBoundaryAdjointCorrectionL P B r b‖ ≤ CQ :=
    norm_firstBoundaryAdjointCorrectionL_le P B r b CB (6*CC) K hr.le hCB (by positivity)
      (zero_le_one.trans hK) hB hNormalZero hBeta
  have hR : ‖radialAdjointTaylorRemainderL Da B r‖ ≤ CJ*r^2 := hTaylor
  have hRemainder : ‖J‖ ≤ CR*r :=
    norm_firstBoundaryAdjointRemainderL_le P C Da B r b (438*CC) K CJ CE hr
      (by positivity) (zero_le_one.trans hK) hCJ hCE hNormalOne hBeta hR hCenter
  refine ⟨J,hCorrection,hRemainder,?_⟩
  intro φ hφ L v hInput
  have hValue := hReal φ hφ L v hInput
  have hDecomp := movingBoundaryHorizontalAdjointL_normal_form P C Da B r b hr.ne'
  have hPoint : movingBoundaryHorizontalAdjointL P C Da r b v = modelBoundaryAdjointL P r b v+
      firstBoundaryAdjointCorrectionL P B r b (sphereSobolevInclusionL 1 0 (by norm_num) v)+J v := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply] using
      congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v) hDecomp
  exact (congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm hPoint) ▸ hValue


/-- The original existential interface, retained for existing callers. -/
theorem uniform_frozen_first_adjoint_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CQ CR : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CB ∧ 0 ≤ CQ ∧ 0 ≤ CR ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,‖B‖ ≤ CB ∧
        ∀ i : I,∃ J : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ‖firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) B
            (d.radius y) (coordDeriv i (fun x => Real.log (d.radius x)) y)‖ ≤ CQ ∧
          ‖J‖ ≤ CR*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (modelBoundaryAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) (d.radius y)
                (coordDeriv i (fun x => Real.log (d.radius x)) y) v+
              firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) B (d.radius y)
                (coordDeriv i (fun x => Real.log (d.radius x)) y)
                  (sphereSobolevInclusionL 1 0 (by norm_num) v)+J v) =ᵐ[sphereProbability]
                    fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  have hTheorem := uniform_frozen_first_adjoint_taylor_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CB,CQ,CR,Q,hη,hCB,hCQ,hCR,hQ,hProduce⟩ := hTheorem
  refine ⟨η,CB,CQ,CR,Q,hη,hCB,hCQ,hCR,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  obtain ⟨B,hCanonical,hB,hDirection⟩ := hHere
  exact ⟨B,hB,hDirection⟩

end ShrinkingSpheres
