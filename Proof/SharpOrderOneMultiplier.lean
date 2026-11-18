import Proof.OrderOneMultiplierProduct
import Proof.EndpointBoundaryCalculus
import Proof.Archive.NativeOrderOneCoefficientMultiplierInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereRotation OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothAngularCasimir
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

lemma norm_rotationVector_unitSphere_le (i j : Fin 3) (w : UnitSphere) :
    ‖rotationVector i j w.val‖ ≤ 2 := by
  have hw : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
  have hi : |w.val i| ≤ 1 := (PiLp.norm_apply_le w.val i).trans_eq hw
  have hj : |w.val j| ≤ 1 := (PiLp.norm_apply_le w.val j).trans_eq hw
  change ‖w.val i • (PiLp.single 2 j (1:ℝ):X)-w.val j • (PiLp.single 2 i (1:ℝ):X)‖ ≤ 2
  calc
    _ ≤ ‖w.val i • (PiLp.single 2 j (1:ℝ):X)‖+‖w.val j • (PiLp.single 2 i (1:ℝ):X)‖ := norm_sub_le _ _
    _ = |w.val i|+|w.val j| := by simp [norm_smul,Real.norm_eq_abs]
    _ ≤ 2 := by linarith only [hi,hj]

theorem norm_smoothSphereValue_rotation_le (m : SmoothData) (q : ℝ) (hq : 0 ≤ q)
    (hD : ∀ w : UnitSphere,‖fderiv ℝ m.1 w.val‖ ≤ q) (i j : Fin 3) :
    ‖smoothSphereValue (smoothRotationData i j m)‖ ≤ 2*q := by
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 2*q)).mpr
  intro w
  change ‖fderiv ℝ m.1 w.val (rotationVector i j w.val)‖ ≤ 2*q
  exact ((fderiv ℝ m.1 w.val).le_opNorm _).trans
    ((mul_le_mul (hD w) (norm_rotationVector_unitSphere_le i j w)
      (norm_nonneg _) hq).trans_eq (by ring))

/-- A sharp-in-regularity H1 multiplier bound. The constant depends only on
    coefficient values and first derivatives on the sphere, even if the
    qualitative H1 realization was constructed using higher smooth jets. -/
theorem norm_orderOneMultiplier_local_C1 (m : SmoothData)
    (T : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (hT : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (T u) =
      coarseSphereScalarMulL (smoothSphereValue m) (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (q : ℝ) (hq : 0 ≤ q)
    (hV : ∀ w : UnitSphere,|m.1 w.val| ≤ q)
    (hD : ∀ w : UnitSphere,‖fderiv ℝ m.1 w.val‖ ≤ q) : ‖T‖ ≤ 73*q := by
  let C := coarseSphereScalarMulL (smoothSphereValue m)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  let Cr (i j : Fin 3) := coarseSphereScalarMulL (smoothSphereValue (smoothRotationData i j m))
  have hC : ‖C‖ ≤ q := (norm_coarseSphereScalarMulL_le _).trans
    ((ContinuousMap.norm_le _ hq).mpr (fun w => hV w))
  have hCr (i j : Fin 3) : ‖Cr i j‖ ≤ 2*q :=
    (norm_coarseSphereScalarMulL_le _).trans (norm_smoothSphereValue_rotation_le m q hq hD i j)
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num),Real.sqrt_nonneg 2]
  have hI (u : SphereSobolev 1) : ‖I u‖ ≤ ‖u‖ :=
    (I.le_opNorm u).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _)).trans_eq (one_mul _))
  have hRot (u : SphereSobolev 1) (i j : Fin 3) : ‖sphereSobolevRotationL 1 i j u‖ ≤ 2*‖u‖ :=
    ((sphereSobolevRotationL 1 i j).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right ((norm_sphereSobolevRotationL_le 1 i j).trans hsqrt) (norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  let v (i j : Fin 3) : SphereSobolev 0 := Cr i j (I u)+C (sphereSobolevRotationL 1 i j u)
  have hv (i j : Fin 3) : ‖v i j‖ ≤ 4*q*‖u‖ := by
    calc
      _ ≤ ‖Cr i j (I u)‖+‖C (sphereSobolevRotationL 1 i j u)‖ := norm_add_le _ _
      _ ≤ (2*q)*‖u‖+q*(2*‖u‖) := add_le_add
        (((Cr i j).le_opNorm _).trans (mul_le_mul (hCr i j) (hI u) (norm_nonneg _) (by positivity)))
        ((C.le_opNorm _).trans (mul_le_mul hC (hRot u i j) (norm_nonneg _) hq))
      _ = _ := by ring
  have hGraph (i j : Fin 3) (k : ℕ) : sphereSobolevCoefficientL 0 k (v i j) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k (T u)) := by
    have hp := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
      (orderOneMultiplier_rotation_product m T hT i j)
    exact (congrArg (sphereSobolevCoefficientL 0 k) hp.symm).trans (orderOneRotation_coefficient (T u) i j k)
  have hCT : ‖I (T u)‖ ≤ q*‖u‖ :=
    (congrArg norm (hT u)).le.trans ((C.le_opNorm _).trans
      (mul_le_mul hC (hI u) (norm_nonneg _) hq))
  have hSum : (∑ i : Fin 3,∑ j : Fin 3,Real.sqrt 2*‖v i j‖) ≤ 72*q*‖u‖ := by
    calc
      _ ≤ ∑ i : Fin 3,∑ j : Fin 3,2*(4*q*‖u‖) := Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => mul_le_mul hsqrt (hv i j) (norm_nonneg _) (by norm_num)))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  exact (norm_sphereSobolev_one_le_rotation_graph (T u) v hGraph).trans
    ((add_le_add hCT hSum).trans_eq (by ring))

/-- The supplied native H1 multiplier therefore has the same local C1 bound;
    its chosen compact extension and higher jet norms do not enter. -/
theorem norm_nativeOrderOneCoefficientMulL_local_C1
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2)
    (q : ℝ) (hq : 0 ≤ q)
    (hV : ∀ w : UnitSphere,|coefficientValue 3 F3 w.val| ≤ q)
    (hD : ∀ w : UnitSphere,‖fderiv ℝ (coefficientValue 3 F3) w.val‖ ≤ q) :
    ‖nativeOrderOneCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace F3 F2 hCoeff‖ ≤ 73*q := by
  apply norm_orderOneMultiplier_local_C1 (nativeH2CoefficientSmoothData F3) _ _ q hq hV hD
  intro u
  exact sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace F3 F2 hCoeff u

end ShrinkingSpheres
