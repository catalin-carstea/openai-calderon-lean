import Proof.ActualFrameCorrectionGraded
import Proof.MatrixCompositionBound
import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The bounded F/F coefficient at every genuine Sobolev grade. -/
def frameCorrectionProductL (s : ℝ) (d : Data) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ i : I,∑ j : I,Q x i j • (firstFrameAdjointCorrectionAtL s d x i).comp
    (firstFrameAdjointCorrectionAtL s d x j)

lemma norm_frameCorrectionProductL_le (s : ℝ) (d : Data) (Q : X → I → I → ℝ)
    (x : X) {B CF : ℝ} (hB : 0 ≤ B) (hCF : 0 ≤ CF)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hF : ∀ i,‖firstFrameAdjointCorrectionAtL s d x i‖ ≤ CF) :
    ‖frameCorrectionProductL s d Q x‖ ≤ 9*B*CF^2 := by
  exact (norm_matrix_composition_sum_le (firstFrameAdjointCorrectionAtL s d x)
    (firstFrameAdjointCorrectionAtL s d x) (Q x) hB hCF hQ hF hF).trans_eq (by ring)

lemma frameCorrectionProductL_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data)
    (Q : X → I → I → ℝ) (x : X) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (frameCorrectionProductL s d Q x u)=
      frameCorrectionProductL t d Q x (sphereSobolevInclusionL s t hst u) := by
  simp only [frameCorrectionProductL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,map_sum,map_smul,firstFrameAdjointCorrectionAtL_inclusion]

lemma Admissible.contDiffOn_frameCorrectionProductL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (s : ℝ)
    (Q : X → I → I → ℝ) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (frameCorrectionProductL s d Q) Y := by
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    ((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK s i).clm_comp
      (hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK s j))))

/-- Exact actual F/F output, using the genuine H1 correction applied in the
    second-trace construction, rather than an unrelated L2 representative. -/
lemma frameCorrectionProductL_actual (d : Data) (Q : X → I → I → ℝ) (x : X)
    (u : SphereSobolev 1) :
    (∑ i : I,∑ j : I,Q x i j • firstFrameAdjointCorrectionL d x i
      (sphereSobolevInclusionL 1 0 (by norm_num) (firstFrameAdjointCorrectionSobolevL d x j u)))=
      frameCorrectionProductL 0 d Q x (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  simp only [frameCorrectionProductL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,firstFrameAdjointCorrectionAtL_zero,firstFrameAdjointCorrectionL_coarse]

def radiusFrameCorrectionProductL (s : ℝ) (d : Data) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  d.radius x • frameCorrectionProductL s d Q x

lemma norm_radiusFrameCorrectionProductL_small (s : ℝ) (d : Data) (Q : X → I → I → ℝ)
    (x : X) {B CF ε : ℝ} (hB : 0 ≤ B) (hCF : 0 ≤ CF)
    (hr : 0 ≤ d.radius x) (hrε : d.radius x ≤ ε)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hF : ∀ i,‖firstFrameAdjointCorrectionAtL s d x i‖ ≤ CF) :
    ‖radiusFrameCorrectionProductL s d Q x‖ ≤ 9*B*CF^2*ε := by
  rw [radiusFrameCorrectionProductL,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  exact ((mul_le_mul_of_nonneg_left (norm_frameCorrectionProductL_le s d Q x hB hCF hQ hF) hr).trans
    (mul_le_mul_of_nonneg_right hrε (by positivity))).trans_eq (by ring)

lemma Admissible.contDiffOn_radiusFrameCorrectionProductL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (s : ℝ)
    (Q : X → I → I → ℝ) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (radiusFrameCorrectionProductL s d Q) Y :=
  hd.2.2.2.2.1.1.smul (hd.contDiffOn_frameCorrectionProductL hY hΩ hK s Q hQ)
end ShrinkingSpheres
