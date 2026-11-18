import Proof.Archive.SphereSobolevTraceReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

lemma norm_sphereTraceReconstructionIdentityL_le :
    ‖sphereSobolevTraceReconstructionIdentityL‖ ≤ 1 := by
  unfold sphereSobolevTraceReconstructionIdentityL
  exact lp.norm_mapCLM_le _ _ _ _

lemma norm_sphereTraceReconstructionRotationL_le (i j : Fin 3) :
    ‖sphereSobolevTraceReconstructionRotationL i j‖ ≤ Real.sqrt 2 := by
  unfold sphereSobolevTraceReconstructionRotationL
  exact lp.norm_mapCLM_le _ _ _ _

/-- The supplied rotation reconstruction also controls H1 by its actual L2
    value and the nine L2 rotation derivatives. No higher derivative enters. -/
theorem norm_sphereSobolev_one_le_rotation_graph
    (u : SphereSobolev 1) (v : Fin 3 → Fin 3 → SphereSobolev 0)
    (hGraph : ∀ i j k,sphereSobolevCoefficientL 0 k (v i j) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)) :
    ‖u‖ ≤ ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖+
      ∑ i : Fin 3,∑ j : Fin 3,Real.sqrt 2*‖v i j‖ := by
  let u0 := sphereSobolevInclusionL 1 0 (by norm_num) u
  let R : SphereSobolev 1 := sphereSobolevTraceReconstructionIdentityL u0+
    ∑ i : Fin 3,∑ j : Fin 3,sphereSobolevTraceReconstructionRotationL i j (v i j)
  have hZero (z : SphereSobolev 0) (k : ℕ) : sphereSobolevCoefficientL 0 k z = z k := by
    simp only [sphereSobolevCoefficientL,neg_zero,besselWeight_zero_order,one_smul]
    rfl
  have hInput (k : ℕ) : sphereSobolevCoefficientL 1 k u = u0 k :=
    (sphereSobolevCoefficientL_inclusion 1 0 (by norm_num) u k).symm.trans (hZero u0 k)
  have hStored (i j : Fin 3) (k : ℕ) : v i j k = harmonicSphereRotation k i j (u0 k) :=
    (hZero (v i j) k).symm.trans ((hGraph i j k).trans (congrArg (harmonicSphereRotation k i j) (hInput k)))
  have hEq : R = u := by
    apply sphereSobolev_ext 1
    intro k
    have hRecon := sphereSobolevTraceReconstruction_stored u0 v hStored k
    have hWeight : besselWeight (-1) k*(1+(k:ℝ)) = 1 := by
      unfold besselWeight
      rw [Real.rpow_neg_one]
      exact inv_mul_cancel₀ (by positivity)
    change besselWeight (-1) k • R k = _
    change besselWeight (-1) k • ((sphereSobolevTraceReconstructionIdentityL u0+
      ∑ i : Fin 3,∑ j : Fin 3,sphereSobolevTraceReconstructionRotationL i j (v i j)) k) = _
    rw [hRecon,smul_smul,hWeight,one_smul]
    exact (hInput k).symm
  have hIdentity : ‖sphereSobolevTraceReconstructionIdentityL u0‖ ≤ ‖u0‖ :=
    (sphereSobolevTraceReconstructionIdentityL.le_opNorm u0).trans
      ((mul_le_mul_of_nonneg_right norm_sphereTraceReconstructionIdentityL_le (norm_nonneg _)).trans_eq (one_mul _))
  have hRot (i j : Fin 3) : ‖sphereSobolevTraceReconstructionRotationL i j (v i j)‖ ≤ Real.sqrt 2*‖v i j‖ :=
    ((sphereSobolevTraceReconstructionRotationL i j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_sphereTraceReconstructionRotationL_le i j) (norm_nonneg _))
  have hSum : ‖∑ i : Fin 3,∑ j : Fin 3,sphereSobolevTraceReconstructionRotationL i j (v i j)‖ ≤
      ∑ i : Fin 3,∑ j : Fin 3,Real.sqrt 2*‖v i j‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => hRot i j))
  exact (congrArg norm hEq).symm.le.trans ((norm_add_le _ _).trans (add_le_add hIdentity hSum))

end ShrinkingSpheres
