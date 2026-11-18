import Proof.ParallelScalarModelMassPoint
import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelRaising
import Proof.ParallelScalarModelBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Pointwise bound after the paired angular degree-gradient cancellation;
all physical coefficient jets use their genuine strong half graphs. -/
theorem scalar_model_degree_remainder_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hf : 1 ≤ floor) (hε : 0 ≤ ε)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj)
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (q : I → I → X → ℝ) (Z0 Z1 : ℝ) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1)
    {y : X} (hy : y ∈ Y) (c : I)
    (hq : ∀ a b,|q a b y| ≤ Z0*ε/beta d.γ d.radius y*metricDensity d.γ y)
    (hDq : ∀ a b,|fderiv ℝ (q a b) y (axis a)| ≤ Z1*ε*metricDensity d.γ y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : DifferentiableAt ℝ U y) :
    let C0 := fun x => (framedRaisingHalfL d x (axis c)).adjoint
    let C1 := fun x => framedRaisingHalfL d x (axis c)
    let U0 := scalarModelDegreeSection U
    let U1 := scalarModelShiftedDegreeSection U
    let H := fun b : I => fiveHalfCovariantDerivative d U (axis b)
    |pairedHalfMassRemainder d q C0 C1 (scalarModelRaisingAdjointHigher A d c)
      (fun x => framedRaisingHigherL d x (axis c)) U0 U1 H y| ≤
      (108*RB.bound*(Z0+Z1))*ε*metricDensity d.γ y*
        (∑ b : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y
          (beta d.γ d.radius y) (axis b)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let H := fun b : I => fiveHalfCovariantDerivative d U (axis b)
  let En := ∑ b : I,halfCovariantDirectionEnergy d U3 y (beta d.γ d.radius y) (axis b)
  let β := beta d.γ d.radius y
  let R := fun x => framedRaisingHalfL d x (axis c)
  let RH := fun x => framedRaisingHigherL d x (axis c)
  let AH := scalarModelRaisingAdjointHigher A d c
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hQ := RB.nonneg
  have hR (a : I) := RB.actual floor ε d hd y hy a c
  have hC0 : ‖(R y).adjoint‖ ≤ RB.bound := by rw [ContinuousLinearMap.adjoint.norm_map];exact (hR 0).1
  have hJU : ‖J (U3 y)‖ ≤ ‖U3 y‖ := (J.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _))
  have hDU : ‖degreeHigherL (U3 y)‖ ≤ 2*‖U3 y‖ := (degreeHigherL.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right norm_degreeHigherL_le_two (norm_nonneg _))
  have hU0 : ‖J (scalarModelDegreeSection U y)‖ ≤ 3*‖U3 y‖ := by
    rw [scalarModelDegreeSection_half_inclusion]
    exact hDU.trans (by nlinarith only [norm_nonneg (U3 y)])
  have hU1 : ‖J (scalarModelShiftedDegreeSection U y)‖ ≤ 3*‖U3 y‖ := by
    change ‖J (scalarModelDegreeSection U y-U3 y)‖ ≤ _
    rw [map_sub,scalarModelDegreeSection_half_inclusion]
    exact (norm_sub_le _ _).trans ((add_le_add hDU hJU).trans_eq (by ring))
  have hDir (b : I) : 0 ≤ halfCovariantDirectionEnergy d U3 y β (axis b) := by
    dsimp only [halfCovariantDirectionEnergy];positivity
  have hSingle (b : I) := Finset.single_le_sum (f:=fun b : I => halfCovariantDirectionEnergy d U3 y β (axis b))
    (fun b _ => hDir b) (Finset.mem_univ b)
  have hV (b : I) : β⁻¹*‖J (H b y)‖^2 ≤ En := by
    rw [fiveHalfCovariantDerivative_half_inclusion d U y (axis b) hU]
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ β*‖U3 y‖^2)).trans (hSingle b)
  have hMass : β*‖U3 y‖^2 ≤ En :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d U3 y (axis 0)‖^2)).trans (hSingle 0)
  have hDC (a b : I) :
      ‖halfOperatorCovariantDerivativeL d R RH y (axis a) (H b y)‖ ≤ RB.bound*‖J (H b y)‖ ∧
      ‖halfOperatorCovariantDerivativeL d (fun x => (R x).adjoint) AH y (axis a) (H b y)‖ ≤ RB.bound*‖J (H b y)‖ := by
    let L := framedRaisingFirstHalfJet d a c y
    have hDR := framed_raising_strong_half_graph hY hΩ hd hK hy a c
    have hRS := ((hd.framedRaisingHalf_smooth (axis c)).1).contDiffAt (hY.mem_nhds hy)
    have hDA := half_covariant_adjoint_strong_extension d R RH AH hRS (axis a)
      (framedRaisingHalf_balanced d y (axis c)) (scalarModelRaisingAdjointHigher_balanced A d c y hA) L hDR
    have hdR := DFunLike.congr_fun hDR (H b y)
    have hdA := DFunLike.congr_fun hDA (H b y)
    simp only [ContinuousLinearMap.comp_apply] at hdR hdA
    rw [hdR,hdA]
    constructor
    · exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hR a).2 (norm_nonneg _))
    · exact (L.adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (by rw [ContinuousLinearMap.adjoint.norm_map];exact (hR a).2) (norm_nonneg _))
  have hTerm (a b : I) := pairedHalfMassRemainderTerm_bound d (q a b) (fun x => (R x).adjoint) R AH RH
    (scalarModelDegreeSection U) (scalarModelShiftedDegreeSection U) (H b) y (axis a) (U3 y)
    Z0 Z1 3 RB.bound RB.bound ε β (metricDensity d.γ y) En hZ0 hZ1 (by norm_num) hQ hQ hε hβ
    (Real.sqrt_nonneg _) (hq a b) (hDq a b) hU0 hU1 hC0 (hR 0).1 (hDC a b).2 (hDC a b).1 (hV b) hMass
  change |∑ a : I,∑ b : I,pairedHalfMassRemainderTerm d (q a b) (fun x => (R x).adjoint) R AH RH
    (scalarModelDegreeSection U) (scalarModelShiftedDegreeSection U) (H b) (axis a) y| ≤ _
  calc
    _ ≤ ∑ a : I,∑ b : I,|pairedHalfMassRemainderTerm d (q a b) (fun x => (R x).adjoint) R AH RH
      (scalarModelDegreeSection U) (scalarModelShiftedDegreeSection U) (H b) (axis a) y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ a : I,∑ b : I,4*3*(Z0*RB.bound+Z1*RB.bound)*ε*metricDensity d.γ y*En :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by dsimp only [En,U3,β];simp only [Fin.sum_univ_three];ring

end ShrinkingSpheres.ParallelEnergy
