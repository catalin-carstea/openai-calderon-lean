import Proof.ParallelNormAssemblyReservedAdjointWeakGraph
import Proof.ParallelScalarFirstHighSections
import Proof.ScalarCovariantAdjointDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

/-- The ACTUAL scalar transpose defect has the retained genuine positive
half representative, paired with the SAME W physical quadratic adjoint. -/
lemma scalar_potential_defect_inner_eq_weak_pair
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) :
    ⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
        (fiveHalfToTwoSection U) y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ)
        (scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y)
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)) := by
  rw [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),
    scalarFiveHalfDefectSection_inclusion d _ _ U hU y,real_inner_comm]

/-- Qualitative integrability of the literal factor-two component is
established from its actual L2 outputs and common support before estimates. -/
theorem scalar_potential_defect_inner_integrable
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (fun y => 2*metricDensity d.γ y*
      ⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
          (fiveHalfToTwoSection U) y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hU20 (x : X) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by
    simp only [fiveHalfToTwoSection,hU0 x hx,map_zero]
  have hDomain := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) (fun x hx => (metricDensity_pos hg hK hx).ne')
    (scalarPrincipalMatrix d.γ d.g₂ d.radius) (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK)
    (fiveHalfToTwoSection U) hU2 S hS.isClosed hSY hU20
  have hSLp : MemLp (scalarCovariantAdjointDefectSection d (metricDensity d.γ)
      (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U)) 2 (volume.restrict Y) :=
    hDomain.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hDomain.2)
  have hQLp := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY hU0 2
  have hPair := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hSLp hQLp
    (fun x _ hx => hDomain.2 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  change Integrable (fun y => 2*metricDensity d.γ y*
    ⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (fiveHalfToTwoSection U) y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) (volume.restrict Y)
  simpa only [mul_assoc] using hPair.const_mul 2

/-- Exact factor2 pointwise Cauchy bound. The scalar positive-half and
quadratic-adjoint negative-half norms have their genuine orientations. -/
lemma abs_scalar_potential_defect_inner_le
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) :
    |2*metricDensity d.γ y*
      ⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
          (fiveHalfToTwoSection U) y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ| ≤
      metricDensity d.γ y*(
        ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y‖^2+
        ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)‖^2) := by
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  let V := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  rw [scalar_potential_defect_inner_eq_weak_pair P W U hU y,
    abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
  have hNorm := abs_sphereSobolevDualPairing_le (1/2:ℝ) F V
  have hSq : 2*‖F‖*‖V‖ ≤ ‖F‖^2+‖V‖^2 := by nlinarith only [sq_nonneg (‖F‖-‖V‖)]
  exact (mul_le_mul_of_nonneg_left hNorm (mul_nonneg (by norm_num) hμ)).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hSq hμ])

end ShrinkingSpheres.ParallelEnergy
