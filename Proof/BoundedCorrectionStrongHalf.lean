import Proof.PhysicalCorrectionCoframeGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A bounded actual L2 operator has this genuine half-domain extension. -/
def halfLiftOfBoundedL2Operator (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
    (B.comp (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)))

lemma halfLiftOfBoundedL2Operator_coarse (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (B.comp (sphereSobolevInclusionL 1 0 (by norm_num)))=
    (halfLiftOfBoundedL2Operator B).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [halfLiftOfBoundedL2Operator,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]

lemma norm_halfLiftOfBoundedL2Operator_le (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) :
    ‖halfLiftOfBoundedL2Operator B‖ ≤ ‖B‖ := by
  have hR : ‖B.comp (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))‖ ≤ ‖B‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg B)).trans_eq (mul_one _))
  unfold halfLiftOfBoundedL2Operator
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _)).trans hR)

/-- Bounded L2 representative of the actual covariant correction jet,
before restricting its input to H1. -/
def physicalFirstCorrectionBoundedCovariantJetL (d : Data) (y a b : X) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j b • firstFrameAdjointCovariantJetL d y a j)+
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j (connection d.γ y a b) • firstFrameAdjointCorrectionL d y j)

lemma physicalFirstCorrectionBoundedCovariantJetL_coarse (d : Data) (y a b : X) :
    (physicalFirstCorrectionBoundedCovariantJetL d y a b).comp (sphereSobolevInclusionL 1 0 (by norm_num))=
      physicalFirstCorrectionCovariantJetL d y a b := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [physicalFirstCorrectionBoundedCovariantJetL,physicalFirstCorrectionCovariantJetL,
    firstFrameCorrectionCoarseFamily,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply]

theorem Admissible.norm_physicalFirstCorrectionBoundedCovariantJetL_frame_le {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i b : I) :
    ‖physicalFirstCorrectionBoundedCovariantJetL d y (d.frame y i) (axis b)‖ ≤
      physicalFirstCorrectionJetBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) := by
  let CC := 9*|M 0| *K
  let CG := 243*K*|M ⟨1,by omega⟩|
  let CΓ := CC*(CG*K)
  let CF := 12*K^2*|M ⟨1,by omega⟩|
  let CT := firstFrameAdjointCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  have hK0 := zero_lt_one.trans_le hK
  have hCC : 0 ≤ CC := by dsimp only [CC];positivity
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hCΓ : 0 ≤ CΓ := mul_nonneg hCC (mul_nonneg hCG hK0.le)
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hEop := hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFrame
  have hE : ‖d.frame y i‖ ≤ K := by
    have hh := (frameVectorLinear d.frame y).le_opNorm (axis i)
    rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at hh
    exact hh.trans hEop
  have hΓ : ‖connectionBilinear d.γ y‖ ≤ CG := hd.1.connection_budget hK0 (by omega) hyΩ
  have hConn : ‖connection d.γ y (d.frame y i) (axis b)‖ ≤ CG*K := by
    rw [← connectionBilinear_apply]
    calc
      _ ≤ ‖connectionBilinear d.γ y‖*‖d.frame y i‖*‖axis b‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ CG*K*1 := by rw [norm_axis];gcongr
      _ = _ := mul_one _
  have hCof (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ CC :=
    hd.1.1.norm_frameCoordinateLinear_le hK hyΩ d.frame hFrame |M 0| (abs_nonneg _)
      (fun a c => (hd.1.reference_entry_bound hyΩ a c).trans (le_abs_self _)) j
  have hc (j : I) : |frameCoordinateLinear d.γ d.frame y j (axis b)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame hyΩ hFrame b j
  have hcΓ (j : I) : |frameCoordinateLinear d.γ d.frame y j (connection d.γ y (d.frame y i) (axis b))| ≤ CΓ := by
    have hh := ((frameCoordinateLinear d.γ d.frame y j).le_opNorm _).trans
      (mul_le_mul (hCof j) hConn (norm_nonneg _) hCC)
    simpa only [Real.norm_eq_abs] using hh
  have hF (j : I) : ‖firstFrameAdjointCorrectionL d y j‖ ≤ CF :=
    hd.norm_firstFrameAdjointCorrectionL_le hΩ hm hK hf hε hε1 hy j
  have hT (j : I) : ‖firstFrameAdjointCovariantJetL d y (d.frame y i) j‖ ≤ CT :=
    hd.norm_firstFrameAdjointCovariantJetL_le hY hΩ hm hK hf hε hε1 hy i j
  exact norm_coframe_covariant_tensor_jet_le d y (d.frame y i) (axis b)
    (fun j => firstFrameAdjointCorrectionL d y j)
    (fun j => firstFrameAdjointCovariantJetL d y (d.frame y i) j)
    hK0.le hCΓ hc hcΓ hF hT

end ShrinkingSpheres
