import Proof.UniformFrozenTraceAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem norm_coarseBoundaryCoefficientMulL_local_C1 (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (h : LocalC1Bound (coefficientValue 2 F) q) :
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))‖ ≤ q := by
  apply (norm_coarseSphereScalarMulL_le _).trans
  apply (ContinuousMap.norm_le _ hq).mpr
  intro w
  exact (h.on_unitSphere (contDiff_coefficientValue 2 F) w).1

/-- Both actual normal multipliers of the fixed-center coefficient have common
    bounds from reference metric values and ellipticity alone. -/
theorem Admissible.fixedCenter_normal_multiplier_norms {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (a : X) :
    ‖oneBoundaryCoefficientMulL (vectorNormalJet (fixedCenterCoefficient Q d.γ d.frame y a))‖ ≤
      438*(9*|M 0| *K)*‖a‖ ∧
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (vectorNormalJet (fixedCenterCoefficient Q d.γ d.frame y a))))‖ ≤ 6*(9*|M 0| *K)*‖a‖ := by
  let C0 := 9*|M 0| *K
  have hC0 : 0 ≤ C0 := by dsimp only [C0];positivity
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hL (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ C0 :=
    hd.1.1.norm_frameCoordinateLinear_le hK hCenter d.frame hFrame |M 0| (abs_nonneg _)
      (fun i l => (hd.1.reference_entry_bound hCenter i l).trans (le_abs_self _)) j
  have hP (j : I) : LocalC1Bound (coefficientValue 2 (fixedCenterCoefficient Q d.γ d.frame y a j)) (C0*‖a‖) := by
    have hLocal := constantBoundaryCoefficient_local_C1 Q hQ (frameCoordinateLinear d.γ d.frame y j a)
    have hValue : |frameCoordinateLinear d.γ d.frame y j a| ≤ C0*‖a‖ :=
      ((frameCoordinateLinear d.γ d.frame y j).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg a))
    intro z hz
    exact ⟨(hLocal z hz).1.trans hValue,(hLocal z hz).2.trans hValue⟩
  have hNormal := vectorNormalJet_local_C1 (fixedCenterCoefficient Q d.γ d.frame y a) (C0*‖a‖) (by positivity) hP
  constructor
  · exact (norm_oneBoundaryCoefficientMulL_local_C1 _ (6*(C0*‖a‖)) (by positivity) hNormal).trans_eq (by
      dsimp only [C0];ring)
  · exact (norm_coarseBoundaryCoefficientMulL_local_C1 _ (6*(C0*‖a‖)) (by positivity) hNormal).trans_eq (by
      dsimp only [C0];ring)

end ShrinkingSpheres
