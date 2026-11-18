import Proof.CoordinateMultiplierSobolev
import Proof.RadialCorrectionDegreeCommutator
import Proof.FirstAdjointCorrectionSobolev

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem radialCorrectionVector_proj (i : I) :
    radialCorrectionVector (EuclideanSpace.proj (𝕜:=ℝ) i) = axis i := by
  ext j
  simp [radialCorrectionVector,axis,eq_comm]

theorem coordinateMultiplierSobolevL_radial (s : ℝ) (i : I) :
    coordinateMultiplierSobolevL s i =
      -radialCorrectionSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i)-
        radialCorrectionAdjointSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i) := by
  simp only [coordinateMultiplierSobolevL,sphereSobolevLinearCoordinateMulL,
    radialCorrectionSobolevL,radialCorrectionAdjointSobolevL,radialCorrectionVector_proj]

def coordinateDegreeCommutatorL (i : I) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)-
    (radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)).adjoint

theorem degree_coordinateMultiplier_commutator (i : I) :
    sphereSobolevDegreeL.comp (coordinateMultiplierSobolevL 1 i)-
      (coordinateMultiplierSobolevL 0 i).comp sphereSobolevDegreeL =
        (coordinateDegreeCommutatorL i).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  let q := EuclideanSpace.proj (𝕜:=ℝ) i
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hR := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (degree_radialCorrection_commutator q)
  have hA := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (degree_radialCorrectionAdjoint_commutator q)
  change sphereSobolevDegreeL (radialCorrectionSobolevL 1 q u)-
      radialCorrectionCovectorL q (sphereSobolevDegreeL u) = -(radialCorrectionCovectorL q (I0 u)) at hR
  change sphereSobolevDegreeL (radialCorrectionAdjointSobolevL 1 q u)-
      (radialCorrectionCovectorL q).adjoint (sphereSobolevDegreeL u) =
        (radialCorrectionCovectorL q).adjoint (I0 u) at hA
  have hR' := sub_eq_iff_eq_add.mp hR
  have hA' := sub_eq_iff_eq_add.mp hA
  change sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 i u)-
    coordinateMultiplierSobolevL 0 i (sphereSobolevDegreeL u) = coordinateDegreeCommutatorL i (I0 u)
  simp only [coordinateMultiplierSobolevL_radial,_root_.sub_apply,_root_.neg_apply,
    radialCorrectionSobolevL_zero,radialCorrectionAdjointSobolevL_zero,map_sub,map_neg,
    coordinateDegreeCommutatorL]
  change -(sphereSobolevDegreeL (radialCorrectionSobolevL 1 q u))-
      sphereSobolevDegreeL (radialCorrectionAdjointSobolevL 1 q u)-
      (-(radialCorrectionCovectorL q (sphereSobolevDegreeL u))-
        (radialCorrectionCovectorL q).adjoint (sphereSobolevDegreeL u)) =
      radialCorrectionCovectorL q (I0 u)-(radialCorrectionCovectorL q).adjoint (I0 u)
  have hSub := congrArg₂ (fun x y : SphereSobolev 0 => -x-y-
    (-(radialCorrectionCovectorL q (sphereSobolevDegreeL u))-
      (radialCorrectionCovectorL q).adjoint (sphereSobolevDegreeL u))) hR' hA'
  apply hSub.trans
  abel

theorem norm_coordinateDegreeCommutatorL_le (i : I) : ‖coordinateDegreeCommutatorL i‖ ≤ 12 := by
  have hProj : ‖(EuclideanSpace.proj (𝕜:=ℝ) i : X →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [PiLp.proj_apply,one_mul] using PiLp.norm_apply_le v i
  have hR : ‖radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)‖ ≤ 6 :=
    (norm_radialCorrectionCovectorL_apply_le _).trans
      ((mul_le_mul_of_nonneg_left hProj (by norm_num : (0:ℝ) ≤ 6)).trans_eq (mul_one _))
  calc
    _ ≤ ‖radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)‖+
        ‖(radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)).adjoint‖ := norm_sub_le _ _
    _ = 2*‖radialCorrectionCovectorL (EuclideanSpace.proj (𝕜:=ℝ) i)‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map];ring
    _ ≤ 12 := by linarith

def firstAdjointCorrectionDegreeCommutatorL (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  firstAdjointCorrectionSobolevL 0 q t i+
    (radialCorrectionCovectorL q).adjoint.comp (coordinateDegreeCommutatorL i)

theorem degree_firstAdjointCorrection_commutator (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    sphereSobolevDegreeL.comp (firstAdjointCorrectionSobolevL 1 q t i)-
      (firstAdjointCorrectionSobolevL 0 q t i).comp sphereSobolevDegreeL =
        (firstAdjointCorrectionDegreeCommutatorL q t i).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let B0 := (radialCorrectionCovectorL q).adjoint
  let B1 := radialCorrectionAdjointSobolevL 1 q
  let M0 := coordinateMultiplierSobolevL 0 i
  let M1 := coordinateMultiplierSobolevL 1 i
  let C := coordinateDegreeCommutatorL i
  have hB (v : SphereSobolev 1) : sphereSobolevDegreeL (B1 v) =
      B0 (I0 v)+B0 (sphereSobolevDegreeL v) := by
    have h := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v)
      (degree_radialCorrectionAdjoint_commutator q)
    change sphereSobolevDegreeL (B1 v)-B0 (sphereSobolevDegreeL v) = B0 (I0 v) at h
    exact sub_eq_iff_eq_add.mp h
  have hM : sphereSobolevDegreeL (M1 u) = C (I0 u)+M0 (sphereSobolevDegreeL u) := by
    have h := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
      (degree_coordinateMultiplier_commutator i)
    change sphereSobolevDegreeL (M1 u)-M0 (sphereSobolevDegreeL u) = C (I0 u) at h
    exact sub_eq_iff_eq_add.mp h
  have hMI : I0 (M1 u) = M0 (I0 u) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics 1 0 (by norm_num) (axis i) u
  have hFirst : sphereSobolevDegreeL (B1 (M1 u)) =
      B0 (M0 (I0 u))+(B0 (C (I0 u))+B0 (M0 (sphereSobolevDegreeL u))) :=
    (hB (M1 u)).trans (congrArg₂ (fun x y : SphereSobolev 0 => x+y)
      (congrArg B0 hMI) ((congrArg B0 hM).trans (map_add B0 _ _)))
  change sphereSobolevDegreeL (firstAdjointCorrectionSobolevL 1 q t i u)-
    firstAdjointCorrectionSobolevL 0 q t i (sphereSobolevDegreeL u) =
      firstAdjointCorrectionDegreeCommutatorL q t i (I0 u)
  simp only [firstAdjointCorrectionSobolevL,firstAdjointCorrectionDegreeCommutatorL,
    radialCorrectionAdjointSobolevL_zero,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,map_add,map_smul]
  change sphereSobolevDegreeL (B1 (M1 u))+t • sphereSobolevDegreeL (B1 u)-
      (B0 (M0 (sphereSobolevDegreeL u))+t • B0 (sphereSobolevDegreeL u)) =
      (B0 (M0 (I0 u))+t • B0 (I0 u))+B0 (C (I0 u))
  have hSub := congrArg₂ (fun x y : SphereSobolev 0 => x+t • y-
    (B0 (M0 (sphereSobolevDegreeL u))+t • B0 (sphereSobolevDegreeL u))) hFirst (hB u)
  apply hSub.trans
  simp only [smul_add]
  abel

theorem norm_firstAdjointCorrectionDegreeCommutatorL_le (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    ‖firstAdjointCorrectionDegreeCommutatorL q t i‖ ≤ 6*‖q‖*(13+|t|) := by
  have hQ := norm_firstAdjointCorrectionSobolevL_zero_le q t i
  have hB : ‖(radialCorrectionCovectorL q).adjoint‖ ≤ 6*‖q‖ := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_radialCorrectionCovectorL_apply_le q
  have hM := norm_coordinateDegreeCommutatorL_le i
  calc
    _ ≤ ‖firstAdjointCorrectionSobolevL 0 q t i‖+
        ‖(radialCorrectionCovectorL q).adjoint.comp (coordinateDegreeCommutatorL i)‖ := norm_add_le _ _
    _ ≤ ‖firstAdjointCorrectionSobolevL 0 q t i‖+
        ‖(radialCorrectionCovectorL q).adjoint‖*‖coordinateDegreeCommutatorL i‖ :=
      add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 6*‖q‖*(1+|t|)+(6*‖q‖)*12 := by gcongr
    _ = _ := by ring

theorem Admissible.norm_firstFrameAdjointDegreeCommutatorL_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i : I) :
    ‖firstAdjointCorrectionDegreeCommutatorL (firstDensityLogCovector d y)
      (d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) i‖ ≤
        84*K^2*|M ⟨1,by omega⟩| := by
  have hQ := hd.1.norm_firstDensityLogCovector_le hΩ hK hm (hd.2.1.center_mem hy)
  have hT := hd.scaled_frame_logRadius_bound hf hε hε1 hy i
  calc
    _ ≤ 6*‖firstDensityLogCovector d y‖*
        (13+|d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)|) :=
      norm_firstAdjointCorrectionDegreeCommutatorL_le _ _ i
    _ ≤ 6*(K^2*|M ⟨1,by omega⟩|)*(13+1) := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
