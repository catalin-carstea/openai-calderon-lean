import Proof.PhysicalCorrectionCoframeEndpoints
import Proof.CoframeOperatorCovariantGraph
import Proof.FirstCorrectionCovariantGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def physicalFirstCorrectionCovariantJetL (d : Data) (y a b : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j b •
    (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num)))+
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j (connection d.γ y a b) •
    firstFrameCorrectionCoarseFamily d j y)

def physicalFirstCorrectionJetBudget (K M0 M1 M2 C2 : ℝ) : ℝ :=
  3*K*firstFrameAdjointCovariantBudget K M1 M2 C2+
    3*((9*|M0| *K)*(243*K*|M1| *K))*(12*K^2*|M1|)

lemma physicalFirstCorrectionJetBudget_nonneg (K M0 M1 M2 C2 : ℝ) (hK : 0 ≤ K) :
    0 ≤ physicalFirstCorrectionJetBudget K M0 M1 M2 C2 := by
  unfold physicalFirstCorrectionJetBudget firstFrameAdjointCovariantBudget firstRadialCovariantBudget
  positivity

theorem Admissible.physicalFirstCorrection_covariant_graph {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a b : X) :
    CoarseCovariantRotationGraph d y a (physicalFirstCorrectionCoarseFamily d b)
      (physicalFirstCorrectionCovariantJetL d y a b) := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (j : I) : DifferentiableAt ℝ (firstFrameCorrectionCoarseFamily d j) y :=
    (((hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK j).clm_comp contDiffOn_const).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp)
  have hG := coframeWeighted_covariant_graph hY d hg hK he hFrame hy a b
    (firstFrameCorrectionCoarseFamily d)
    (fun j => (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
    hD (fun j => hd.firstFrameCorrectionCoarseFamily_covariant_graph hY hΩ hK hy a j)
  exact hG.congr_germ (Eventually.of_forall (fun x => (physicalFirstCorrectionCoarseFamily_eq d b x).symm))

theorem Admissible.norm_physicalFirstCorrectionCovariantJetL_frame_le {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i b : I) :
    ‖physicalFirstCorrectionCovariantJetL d y (d.frame y i) (axis b)‖ ≤
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
  have hF (j : I) : ‖firstFrameCorrectionCoarseFamily d j y‖ ≤ CF := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (firstFrameAdjointCorrectionL d y j))).trans_eq (mul_one _)).trans
          (hd.norm_firstFrameAdjointCorrectionL_le hΩ hm hK hf hε hε1 hy j))
  have hT (j : I) : ‖(firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CT := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (firstFrameAdjointCovariantJetL d y (d.frame y i) j))).trans_eq (mul_one _)).trans
          (hd.norm_firstFrameAdjointCovariantJetL_le hY hΩ hm hK hf hε hε1 hy i j))
  exact norm_coframe_covariant_tensor_jet_le d y (d.frame y i) (axis b)
    (fun j => firstFrameCorrectionCoarseFamily d j y)
    (fun j => (firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
    hK0.le hCΓ hc hcΓ hF hT
end ShrinkingSpheres
