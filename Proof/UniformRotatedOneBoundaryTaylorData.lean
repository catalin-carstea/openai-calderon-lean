import Proof.RotatedCoefficientPairGerms
import Proof.UniformNormalizedRotationRemainder
import Proof.CommonSupportRotationPerturbation
import Proof.AffineCoefficientGenerator
import Proof.CommonSupportOneBoundaryTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Genuine rotated normalized coefficients have principal and quadratic
coarse/H1 normal and tangential adjoint derivative bounds. -/
theorem uniform_rotated_one_boundary_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 CQ : ℝ,0 < η ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∀ B0 : X → Mat,ContDiff ℝ ∞ B0 → HasCompactSupport B0 →
      (∀ z ∈ Metric.closedBall (0:X) 2,B0 =ᶠ[𝓝 z] normalizedFirstNormalCoefficient d y) →
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      (∀ t z,z ∈ Metric.closedBall (0:X) 2 → A =ᶠ[𝓝 (t,z)]
        (fun p : ℝ × X => coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => normalizedFirstNormalCoefficient d y v.2) ((p.1,0),p.2))) ∧
      (∀ t z,z ∈ Metric.closedBall (0:X) 2 → A1 =ᶠ[𝓝 (t,z)]
        (fun p : ℝ × X => firstDensityLogCovector d y (coordinateRotation i j p.1 p.2) • (1:Mat))) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      CommonSupportOneBoundaryDerivativeBounds A1 hA1 S hS hz1 C1 ∧
      CommonSupportOneBoundaryDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2) ∧
      CommonSupportOneBoundaryDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y) ∧
      CommonSupportOneBoundaryTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) (CQ*(d.radius y)^2) := by
  obtain ⟨η,CQ,hη,hCQ,hRot⟩ := uniform_normalized_coefficient_rotation_remainder_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  let PG := K^2*|M ⟨1,by omega⟩|
  let C1 := 14*PG
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1];positivity
  refine ⟨min η 1,C1,CQ,lt_min hη zero_lt_one,hC1,hCQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j B0 hB0 hCompact0 hRep0
  let ell := firstDensityLogCovector d y
  let r := d.radius y
  let R := normalizedFirstCoefficientRemainder d y
  have hEll : ‖ell‖ ≤ PG := hd.1.norm_firstDensityLogCovector_le hΩ hK (by omega) (hd.2.1.center_mem hy)
  have hN1 : 14*‖ell‖ ≤ C1 := mul_le_mul_of_nonneg_left hEll (by norm_num)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,hRep,hRep1,hField,hRepD⟩ :=
    exists_rotated_coefficient_pair_germs (normalizedFirstNormalCoefficient d y) B0 hB0 hCompact0 hRep0 ell r i j
  let R1 : X → Mat := fun z => ell z • (1:Mat)
  have hR1 : ContDiff ℝ ∞ R1 := ell.contDiff.smul contDiff_const
  have hFirstRep (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : A1 =ᶠ[𝓝 ((0:ℝ),z)]
      (fun p : ℝ × X => (0:Mat)+coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R1 v.2) ((p.1,0),p.2)) := by
    filter_upwards [hRep1 0 z hzB] with p hp
    exact hp.trans (by simpa only [zero_add] using (coordinateRotationPrincipalFamily_scalar i j ell p.1 p.2).symm)
  have hFirstBounds (z : X) (hzB : z ∈ (ballOpens:Set X)) := affineScalar_rotation_generator_C1 i j ell z hzB
  obtain ⟨b1,hb1,hzb1,hCurve1,hV1,hD1⟩ := commonSupport_rotation_perturbation_generators A1 hA1 S hS hz1 R1 0 i j
    (fun z _ => hasDerivAt_coordinateRotationPrincipal_zero i j R1 z (hR1.differentiable (by simp) z))
    hFirstRep C1 hC1 (fun z hzB => (hFirstBounds z hzB).1.trans hN1) (fun z hzB => (hFirstBounds z hzB).2.trans hN1)
  have hRHere (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :=
    hRot floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy i j z hzB
  obtain ⟨bD,hbD,hzbD,hCurveD,hVD,hDD⟩ := commonSupport_rotation_perturbation_generators D hD S hS hzD R 1 i j
    (fun z hzB => (hRHere z hzB).1) (fun z hzB => hRepD 0 z hzB) (CQ*r^2) (by positivity)
    (fun z hzB => (hRHere z (unitBall_subset_closedBall_two hzB)).2.1)
    (fun z hzB => (hRHere z (unitBall_subset_closedBall_two hzB)).2.2)
  have hB1 := commonSupport_one_boundary_derivatives_of_generator_bounds A1 hA1 S hS hz1 b1 hb1 hzb1 hCurve1 C1 hC1 hV1 hD1
  have hBD := commonSupport_one_boundary_derivatives_of_generator_bounds D hD S hS hzD bD hbD hzbD hCurveD (CQ*r^2) (by positivity) hVD hDD
  obtain ⟨bA,hbA,hzbA,hCurveA,hVA,hDA⟩ := commonSupport_affine_generator_bounds A A1 D S r C1 CQ hr.le hr1 hC1 hCQ
    hField b1 bD hb1 hbD hzb1 hzbD hCurve1 hCurveD hV1 hD1 hVD hDD
  have hBA := commonSupport_one_boundary_derivatives_of_generator_bounds A hA S hS hz bA hbA hzbA hCurveA ((C1+CQ)*r) (by positivity) hVA hDA
  have hScalar (t : ℝ) (_ht : t ∈ (Set.univ:Set ℝ)) (w : UnitSphere) :
      A1 (t,w.val) = ell (coordinateRotation i j t w.val) • (1:Mat) :=
    (hRep1 t w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))).eq_of_nhds
  have hTaylor := commonSupport_one_boundary_taylor_derivatives A A1 D hA hA1 hD S S S hS hS hS hz hz1 hzD
    r (CQ*r^2) hField Set.univ isOpen_univ (mem_univ _) (fun t z => ell (coordinateRotation i j t z)) hScalar hBD
  exact ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,hRep,hRep1,hField,hB1,hBD,hBA,hTaylor⟩

end ShrinkingSpheres
