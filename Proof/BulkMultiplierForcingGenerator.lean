import Proof.SmoothMultiplierForcingGenerator
import Proof.MultiplierForcingAffine
import Proof.Archive.CommonSupportMatrixInverse
import Proof.MatrixFieldJetNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma nativeBulkMultiplierForcing_eq_columns_rows
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (C : I → SmoothCoefficientJets 2) (R : I → SmoothCoefficientJets 1)
    (hC : ∀ i,∀ z ∈ (ballOpens:Set X),coefficientValue 2 (C i) z =
      ∑ j : I,coefficientValue 2 (F i j) z*(gradient (coefficientValue 3 Q) z) j)
    (hR : ∀ j,∀ z ∈ (ballOpens:Set X),coefficientValue 1 (R j) z =
      ∑ i : I,coefficientValue 2 (F i j) z*(gradient (coefficientValue 3 Q) z) i) :
    nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q =
      nativeSmoothMultiplierForcingL fixedSobolevCalculus C R 0 := by
  rw [nativeBulkMultiplierForcing_zero_drift,nativeSmoothMultiplierForcing_zero_mass]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun A : BallH1 →L[ℝ] BallH1 => (unitBallCoordinateGradientL i).comp A)
    unfold nativeCoefficientH1ProductL
    rw [coefficientMultiplier_congr_on_ball fixedSobolevCalculus 1 (smoothMultiplierColumnJets F Q i) (C i)
      (by intro z hz;rw [coefficientValue_smoothMultiplierColumnJets];exact (hC i z hz).symm)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [coefficientMultiplier_congr_on_ball fixedSobolevCalculus 0 (smoothMultiplierRowJets F Q j) (R j)
      (by intro z hz;change coefficientValue 1 (smoothMultiplierRowJets F Q j) z = _
          rw [coefficientValue_smoothMultiplierRowJets];exact (hR j z hz).symm)]

/-- The actual bulk multiplier forcing differentiates to the SAME native
forcing of the compact coefficient generator, for fixed arbitrary multiplier. -/
theorem hasDerivAt_commonSupport_bulkMultiplierForcing
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0)
    (b : X → Mat) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hSlice : ∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0) (Q : SmoothCoefficientJets 3) :
    let bb : ℝ × X → Mat := fun p => b p.2
    let hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
    let hzbb : ∀ t z,z ∉ S → bb (t,z) = 0 := fun _ z h => hzb z h
    HasDerivAt (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus
      (commonSupportMatrixFamily 2 a ha S hS hz t) (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus
        (commonSupportMatrixFamily 2 bb hbb S hS hzbb 0) (fun _ => 0) Q) 0 := by
  dsimp only
  let bb : ℝ × X → Mat := fun p => b p.2
  have hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
  have hzbb : ∀ t z,z ∉ S → bb (t,z) = 0 := fun _ z h => hzb z h
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let G := commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
  let C := fun (i : I) (p : ℝ × X) => ∑ j : I,a p i j*(gradient (coefficientValue 3 Q) p.2) j
  let R := fun (j : I) (p : ℝ × X) => ∑ i : I,a p i j*(gradient (coefficientValue 3 Q) p.2) i
  let bC := fun (i : I) (z : X) => ∑ j : I,b z i j*(gradient (coefficientValue 3 Q) z) j
  let bR := fun (j : I) (z : X) => ∑ i : I,b z i j*(gradient (coefficientValue 3 Q) z) i
  have hC (i : I) : ContDiff ℝ ∞ (C i) := ContDiff.sum (fun j (_ : j ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp ha i) j).mul ((contDiff_multiplier_gradient_coordinate Q j).comp contDiff_snd))
  have hR (j : I) : ContDiff ℝ ∞ (R j) := ContDiff.sum (fun i (_ : i ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp ha i) j).mul ((contDiff_multiplier_gradient_coordinate Q i).comp contDiff_snd))
  have hbC (i : I) : ContDiff ℝ ∞ (bC i) := ContDiff.sum (fun j (_ : j ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp hb i) j).mul (contDiff_multiplier_gradient_coordinate Q j))
  have hbR (j : I) : ContDiff ℝ ∞ (bR j) := ContDiff.sum (fun i (_ : i ∈ Finset.univ) =>
    (contDiff_pi.mp (contDiff_pi.mp hb i) j).mul (contDiff_multiplier_gradient_coordinate Q i))
  have hzC (i : I) (t : ℝ) (z : X) (hzS : z ∉ S) : C i (t,z) = 0 := by simp [C,hz t z hzS]
  have hzR (j : I) (t : ℝ) (z : X) (hzS : z ∉ S) : R j (t,z) = 0 := by simp [R,hz t z hzS]
  have hzbC (i : I) (z : X) (hzS : z ∉ S) : bC i z = 0 := by simp [bC,hzb z hzS]
  have hzbR (j : I) (z : X) (hzS : z ∉ S) : bR j z = 0 := by simp [bR,hzb z hzS]
  have hEntry (i j : I) (z : X) : HasDerivAt (fun t => a (t,z) i j) (b z i j) 0 := by
    simpa only [Function.comp_def,matrixEntryL_apply] using (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hSlice z)
  have hSliceC (i : I) (z : X) : HasDerivAt (fun t => C i (t,z)) (bC i z) 0 :=
    HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => (hEntry i j z).mul_const ((gradient (coefficientValue 3 Q) z) j))
  have hSliceR (j : I) (z : X) : HasDerivAt (fun t => R j (t,z)) (bR j z) 0 :=
    HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (hEntry i j z).mul_const ((gradient (coefficientValue 3 Q) z) i))
  let CF := fun (t : ℝ) i => commonSupportCoefficientFamily 2 (C i) (hC i) S hS (hzC i) t
  let RF := fun (t : ℝ) j => commonSupportCoefficientFamily 1 (R j) (hR j) S hS (hzR j) t
  let CG := fun i => compactCoefficient 2 (bC i) (hbC i) (HasCompactSupport.intro hS (hzbC i))
  let RG := fun j => compactCoefficient 1 (bR j) (hbR j) (HasCompactSupport.intro hS (hzbR j))
  have hFVal (t : ℝ) (z : X) (i j : I) : coefficientValue 2 (F t i j) z = a (t,z) i j :=
    congrArg (fun A : Mat => A i j) (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 a ha S hS hz t) z)
  have hGVal (z : X) (i j : I) : coefficientValue 2 (G i j) z = b z i j :=
    congrArg (fun A : Mat => A i j) (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 bb hbb S hS hzbb 0) z)
  have hFun : (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q) =
      fun t => nativeSmoothMultiplierForcingL fixedSobolevCalculus (CF t) (RF t) 0 := by
    funext t
    apply nativeBulkMultiplierForcing_eq_columns_rows
    · intro i z hzB
      rw [coefficientValue_commonSupportCoefficientFamily]
      simp only [hFVal]
      rfl
    · intro j z hzB
      rw [coefficientValue_commonSupportCoefficientFamily]
      simp only [hFVal]
      rfl
  have hGen : nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus G (fun _ => 0) Q =
      nativeSmoothMultiplierForcingL fixedSobolevCalculus CG RG 0 := by
    apply nativeBulkMultiplierForcing_eq_columns_rows
    · intro i z hzB
      rw [coefficientValue_compactCoefficient]
      simp only [hGVal]
      rfl
    · intro j z hzB
      rw [coefficientValue_compactCoefficient]
      simp only [hGVal]
      rfl
  change HasDerivAt (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q)
    (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus G (fun _ => 0) Q) 0
  rw [hFun,hGen]
  exact hasDerivAt_commonSupport_smoothMultiplierForcing C R hC hR S hS hzC hzR bC bR hbC hbR hzbC hzbR hSliceC hSliceR

end ShrinkingSpheres
