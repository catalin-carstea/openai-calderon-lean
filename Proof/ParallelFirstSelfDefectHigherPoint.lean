import Proof.ParallelFirstSelfCompleteAdjointJet
import Proof.ParallelFirstSelfCoreSplit
import Proof.HalfScalarTransposeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- A pointwise positive-half representative of the actual complete
adjoint defect. Its derivative witnesses need no measurability. -/
def firstAdjointDefectHigherPoint {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (H : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev (1/2:ℝ) :=
  ∑ b : I,(-H b (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))-
    ((metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)) •
      WF.covariantCoordinateAdjointHigher b y
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))

lemma firstAdjointDefectHigherPoint_graph
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y)
    (H : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : ∀ b,WF.effectiveAdjointCovariantDerivative b b y=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H b)) :
    firstAdjointDefectCoreSection P WF W U y=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (firstAdjointDefectHigherPoint WF H U y) := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  rw [firstAdjointDefectCoreSection_graph hY hΩ hSub hd hK P WF W U hU hy,
    sphereSobolevInclusionL_trans_apply]
  unfold firstAdjointDefectHigherPoint
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hA := DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hy)
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hA
  change -WF.effectiveAdjointCovariantDerivative b b y _-_= _
  rw [hH b]
  simp only [ContinuousLinearMap.comp_apply,map_sub,map_neg,map_smul,hA]

lemma norm_firstAdjointDefectHigherPoint_le
    {P : PhysicalPrincipalData Y d CF CT} (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (H : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    {CA CJ CQ : ℝ} (hCA : 0 ≤ CA) (hCQ : 0 ≤ CQ) (hε : 0 ≤ ε)
    (hA : ∀ b,‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε)
    (hH : ∀ b,‖H b‖ ≤ CJ*ε)
    (hq : ∀ b,|(metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)| ≤ CQ) :
    ‖firstAdjointDefectHigherPoint WF H U y‖ ≤
      (3*(CJ+CQ*CA))*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖ := by
  let V := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  have hHN (b : I) : ‖H b V‖ ≤ (CJ*ε)*‖V‖ :=
    ((H b).le_opNorm V).trans (mul_le_mul_of_nonneg_right (hH b) (norm_nonneg V))
  have hAN (b : I) : ‖WF.covariantCoordinateAdjointHigher b y V‖ ≤ (CA*ε)*‖V‖ :=
    ((WF.covariantCoordinateAdjointHigher b y).le_opNorm V).trans
      (mul_le_mul_of_nonneg_right (hA b) (norm_nonneg V))
  change ‖∑ b : I,(-H b V-((metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)) •
    WF.covariantCoordinateAdjointHigher b y V)‖ ≤ (3*(CJ+CQ*CA))*ε*‖V‖
  calc
    _ ≤ ∑ b : I,‖-H b V-((metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)) •
        WF.covariantCoordinateAdjointHigher b y V‖ := norm_sum_le _ _
    _ ≤ ∑ _b : I,((CJ+CQ*CA)*ε)*‖V‖ := Finset.sum_le_sum (fun b _ => by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg,norm_smul,Real.norm_eq_abs]
      exact (add_le_add (hHN b) (mul_le_mul (hq b) (hAN b) (norm_nonneg _) hCQ)).trans_eq (by ring))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres.ParallelEnergy
