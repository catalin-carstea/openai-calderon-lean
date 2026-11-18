import Proof.BulkMultiplierForcingGenerator
import Proof.Archive.SmoothCommonSupportStrongOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The genuine multiplier forcing is smooth in every finite-dimensional
common-support parameter, for each fixed smooth scalar multiplier. This is
qualitative regularity of the same native operator used in the gain bounds. -/
theorem contDiff_commonSupport_bulkMultiplierForcing
    (A : P × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0) (Q : SmoothCoefficientJets 3) :
    ContDiff ℝ ∞ (fun p => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus
      (commonSupportMatrixFamily 2 A hA S hS hz p) (fun _ => 0) Q) := by
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let C := fun (i : I) (p : P × X) => ∑ j : I,A p i j*(gradient (coefficientValue 3 Q) p.2) j
  let R := fun (j : I) (p : P × X) => ∑ i : I,A p i j*(gradient (coefficientValue 3 Q) p.2) i
  have hC (i : I) : ContDiff ℝ ∞ (C i) := ContDiff.sum (fun j (_ : j ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul ((contDiff_multiplier_gradient_coordinate Q j).comp contDiff_snd))
  have hR (j : I) : ContDiff ℝ ∞ (R j) := ContDiff.sum (fun i (_ : i ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul ((contDiff_multiplier_gradient_coordinate Q i).comp contDiff_snd))
  have hzC (i : I) (p : P) (z : X) (hzS : z ∉ S) : C i (p,z) = 0 := by simp [C,hz p z hzS]
  have hzR (j : I) (p : P) (z : X) (hzS : z ∉ S) : R j (p,z) = 0 := by simp [R,hz p z hzS]
  let CF := fun (p : P) i => commonSupportCoefficientFamily 2 (C i) (hC i) S hS (hzC i) p
  let RF := fun (p : P) j => commonSupportCoefficientFamily 1 (R j) (hR j) S hS (hzR j) p
  have hFVal (p : P) (z : X) (i j : I) : coefficientValue 2 (F p i j) z = A (p,z) i j :=
    congrArg (fun M : Mat => M i j) (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz p) z)
  have hFun : (fun p => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F p) (fun _ => 0) Q) =
      fun p => nativeSmoothMultiplierForcingL fixedSobolevCalculus (CF p) (RF p) 0 := by
    funext p
    apply nativeBulkMultiplierForcing_eq_columns_rows
    · intro i z hzB
      rw [coefficientValue_commonSupportCoefficientFamily]
      simp only [hFVal]
      rfl
    · intro j z hzB
      rw [coefficientValue_commonSupportCoefficientFamily]
      simp only [hFVal]
      rfl
  have hProd (i : I) : ContDiff ℝ ∞ (fun p => nativeCoefficientH1ProductL fixedSobolevCalculus (CF p i)) := by
    have hMult := contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 1 (C i) (hC i) S hS (hzC i)
    exact contDiff_const.clm_comp hMult
  have hRow (j : I) : ContDiff ℝ ∞ (fun p => coefficientMultiplier fixedSobolevCalculus 0 (RF p j)) :=
    contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0 (R j) (hR j) S hS (hzR j)
  have hLeft : ContDiff ℝ ∞ (fun p => ∑ i : I,(unitBallCoordinateGradientL i).comp
      (nativeCoefficientH1ProductL fixedSobolevCalculus (CF p i))) :=
    ContDiff.sum (fun i _ => contDiff_const.clm_comp (hProd i))
  have hRight : ContDiff ℝ ∞ (fun p => ∑ j : I,(coefficientMultiplier fixedSobolevCalculus 0 (RF p j)).comp
      (unitBallCoordinateGradientL j)) :=
    ContDiff.sum (fun j _ => (hRow j).clm_comp contDiff_const)
  rw [hFun]
  exact (hLeft.add hRight).sub contDiff_const

end ShrinkingSpheres
