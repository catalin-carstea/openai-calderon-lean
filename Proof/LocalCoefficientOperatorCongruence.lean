import Proof.SharpStrongOperator
import Proof.FullCoefficientEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] strongCoefficientOperatorL fullCoefficientOperatorL

/-- The actual strong/full divergence maps depend only on their coefficient
    values on the open unit ball. Exterior cutoffs and higher jet witnesses
    cannot change these maps. -/
theorem coefficientOperators_eq_of_unitBall (hcalc : FixedSobolevCalculus)
    (F G : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z) :
    strongDirichletOperator hcalc 0 F = strongDirichletOperator hcalc 0 G ∧
      fullCoefficientOperatorL hcalc 0 F = fullCoefficientOperatorL hcalc 0 G := by
  have hZero (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      coefficientValue 2 ((F-G) i j) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [ballOpens.isOpen.mem_nhds hz] with w hw
    have h := congrArg (fun A : Mat => A i j) (hField w hw)
    change coefficientValue 2 (F i j) w = coefficientValue 2 (G i j) w at h
    change coefficientValue 2 (F i j) w-coefficientValue 2 (G i j) w = 0
    exact sub_eq_zero.mpr h
  have hv (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) : |coefficientValue 2 ((F-G) i j) z| ≤ 0 := by
    rw [(hZero i j z hz).eq_of_nhds,abs_zero]
  have hd (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      ‖fderiv ℝ (coefficientValue 2 ((F-G) i j)) z‖ ≤ 0 := by
    rw [(hZero i j z hz).fderiv_eq,fderiv_const_apply,norm_zero]
  have hS := norm_strongDirichletOperator_zero_sub_le hcalc F G 0 le_rfl hv hd
  have hF := norm_fullCoefficientOperator_zero_le hcalc (F-G) 0 le_rfl hv hd
  rw [mul_zero] at hS hF
  have hZeroS := norm_le_zero_iff.mp hS
  have hZeroF := norm_le_zero_iff.mp hF
  constructor
  · exact sub_eq_zero.mp hZeroS
  · apply sub_eq_zero.mp
    exact ((fullCoefficientOperatorL hcalc 0).map_sub F G).symm.trans hZeroF

/-- A true affine coefficient decomposition on the ball is the same affine
    decomposition of the native operators, with one shared remainder witness. -/
theorem coefficientOperators_affine_identity (hcalc : FixedSobolevCalculus)
    (F F0 F1 R : SmoothCoefficientMatrix 2) (r : ℝ)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 R z =
      coefficientMatrixField 2 F z-coefficientMatrixField 2 F0 z-r • coefficientMatrixField 2 F1 z) :
    strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 F0-
        r • strongDirichletOperator hcalc 0 F1 = strongDirichletOperator hcalc 0 R ∧
      fullCoefficientOperatorL hcalc 0 F-fullCoefficientOperatorL hcalc 0 F0-
        r • fullCoefficientOperatorL hcalc 0 F1 = fullCoefficientOperatorL hcalc 0 R := by
  have hEq : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F-F0-r • F1) z =
      coefficientMatrixField 2 R z := by
    intro z hz
    rw [hField z hz]
    ext i j
    rfl
  obtain ⟨hS,hF⟩ := coefficientOperators_eq_of_unitBall hcalc (F-F0-r • F1) R hEq
  constructor
  · change (strongCoefficientOperatorL hcalc 0) F-(strongCoefficientOperatorL hcalc 0) F0-
        r • (strongCoefficientOperatorL hcalc 0) F1 = _
    have hMap : (strongCoefficientOperatorL hcalc 0) (F-F0-r • F1) =
        (strongCoefficientOperatorL hcalc 0) F-(strongCoefficientOperatorL hcalc 0) F0-
          r • (strongCoefficientOperatorL hcalc 0) F1 := by
      simp only [(strongCoefficientOperatorL hcalc 0).map_sub,(strongCoefficientOperatorL hcalc 0).map_smul]
    exact hMap.symm.trans hS
  · have hMap : (fullCoefficientOperatorL hcalc 0) (F-F0-r • F1) =
        (fullCoefficientOperatorL hcalc 0) F-(fullCoefficientOperatorL hcalc 0) F0-
          r • (fullCoefficientOperatorL hcalc 0) F1 := by
      simp only [(fullCoefficientOperatorL hcalc 0).map_sub,(fullCoefficientOperatorL hcalc 0).map_smul]
    exact hMap.symm.trans hF

end ShrinkingSpheres
