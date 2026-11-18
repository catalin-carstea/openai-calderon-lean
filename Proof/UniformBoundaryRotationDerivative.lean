import Proof.RotatedBoundaryMultiplierDerivative
import Proof.OrthogonalAffineCoefficient
import Proof.UniformRotatedWeakEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

/-- The actual first scalar model has a normal multiplier derivative bounded
    by its covector norm, for any compact whole-angle representative. -/
theorem norm_fderiv_rotated_scalar_commonSupport_normal_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (i j : I) (ell : X →L[ℝ] ℝ)
    (hRep : ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) =
      ell (coordinateRotation i j θ z) • (1:Mat)) :
    ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL
      (normalCoefficientJetsFamily a ha S hS hz θ)) 0‖ ≤
        boundaryHalfDerivativeBudget*(36*(14*‖ell‖)) := by
  let R : X → Mat := fun z => ell z • (1:Mat)
  have hR : ContDiff ℝ ∞ R := ell.contDiff.smul contDiff_const
  have hRepR (θ : ℝ) (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      a (θ,z) = coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((θ,0),z) := by
    rw [hRep θ z hzB,coordinateRotationPrincipalFamily_scalar]
  have hBound := affineScalar_rotation_generator_C1 i j ell
  exact (norm_fderiv_rotated_commonSupport_boundary_matrix_le a ha S hS hz R i j
    (fun z _ => hR.differentiable (by simp) z) hRepR (14*‖ell‖) (by positivity)
    (fun z hzB => (hBound z hzB).1) (fun z hzB => (hBound z hzB).2)).1

/-- Every actual compact representative of the geometric quadratic coefficient
    remainder has uniform quadratic normal/tangent multiplier angle derivatives.
    This includes any witnesses already chosen for another actual endpoint. -/
theorem uniform_actual_boundary_remainder_rotation_derivative {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∀ a : ℝ × X → Mat,∀ ha : ContDiff ℝ ∞ a,∀ S : Set X,∀ hS : IsCompact S,
      ∀ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => firstCoefficientRemainder d y v.2) ((θ,0),z)) →
      ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)) 0‖ ≤ C*(d.radius y)^2 ∧
        ∀ k : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz k θ)) 0‖ ≤ C*(d.radius y)^2 := by
  have hCompactTheorem := uniform_actual_compact_firstCoefficientRemainder hY hΩ
    (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hCompact⟩ := hCompactTheorem
  have hRotationTheorem := uniform_first_coefficient_rotation_remainder_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,Q,hηR,hQ,hRotation⟩ := hRotationTheorem
  let B := boundaryHalfDerivativeBudget
  let CM := B*(36*Q)
  let CT := B*(78*Q)
  let C := CM+CT
  have hB : 0 ≤ B := boundaryHalfDerivativeBudget_nonneg
  have hCM : 0 ≤ CM := by dsimp [CM];positivity
  have hCT : 0 ≤ CT := by dsimp [CT];positivity
  refine ⟨min ηB ηR,C,lt_min hηB hηR,add_nonneg hCM hCT,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j a ha S hS hz hRep
  have hCompactPoint := hCompact floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨A,hA,hSupport,hAgree⟩ := hCompactPoint
  have hRDiff (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      DifferentiableAt ℝ (firstCoefficientRemainder d y) z :=
    (hA.differentiable (by simp) z).congr_of_eventuallyEq (hAgree z hzB).symm
  have hAt (z : X) (hzB : z ∈ (ballOpens:Set X)) := hRotation floor hf ε hε
    (hSmall.trans (min_le_right _ _)) d hd y hy i j z (unitBall_subset_closedBall_two hzB)
  have hBound := norm_fderiv_rotated_commonSupport_boundary_matrix_le a ha S hS hz
    (firstCoefficientRemainder d y) i j hRDiff hRep (Q*(d.radius y)^2) (by positivity)
    (fun z hzB => (hAt z hzB).2.1) (fun z hzB => (hAt z hzB).2.2)
  have hN : boundaryHalfDerivativeBudget*(36*(Q*(d.radius y)^2)) ≤ C*(d.radius y)^2 := by
    have hle := mul_le_mul_of_nonneg_right (show CM ≤ C from le_add_of_nonneg_right hCT) (sq_nonneg (d.radius y))
    convert hle using 1 <;> dsimp [CM,B] <;> ring
  have hT : boundaryHalfDerivativeBudget*(78*(Q*(d.radius y)^2)) ≤ C*(d.radius y)^2 := by
    have hle := mul_le_mul_of_nonneg_right (show CT ≤ C from le_add_of_nonneg_left hCM) (sq_nonneg (d.radius y))
    convert hle using 1 <;> dsimp [CT,B] <;> ring
  exact ⟨hBound.1.trans hN,fun k => (hBound.2 k).trans hT⟩

end ShrinkingSpheres
