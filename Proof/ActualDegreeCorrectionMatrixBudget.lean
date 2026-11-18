import Proof.FirstCorrectionMatrixCross
import Proof.ActualCorrectionProductBudget
import Proof.ScaledFrameLogRadiusSmall
import Proof.FlatRaisingHigherAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalDegreeCorrectionCrossL (d : Data) (x : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  firstCorrectionMatrixCrossL d
    (fun i x => scaledFrameLogRadius d.radius d.frame i x • sphereSobolevDegreeL)
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

lemma Admissible.norm_principalDegreeCorrectionCrossL_small {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖principalDegreeCorrectionCrossL d y‖ ≤
      162*(K+1)*K^2*(firstCorrectionGradeBound 1 K (M ⟨1,by omega⟩)+
        firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩))*ε := by
  let C0 := firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩)
  let C1 := firstCorrectionGradeBound 1 K (M ⟨1,by omega⟩)
  have hC0 : 0 ≤ C0 := firstCorrectionGradeBound_nonneg 0 K _
  have hB : 0 ≤ 9*(K+1)*K^2 := by positivity
  have hCA : 0 ≤ 2*ε := by positivity
  have hF0 (i : I) : ‖firstFrameAdjointCorrectionL d y i‖ ≤ C0 := by
    rw [← firstFrameAdjointCorrectionAtL_zero]
    exact hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 0 hy i
  have hF1 (i : I) : ‖firstFrameAdjointCorrectionSobolevL d y i‖ ≤ C1 :=
    hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 1 hy i
  have hD : ‖sphereSobolevDegreeL‖ ≤ 2 := by
    simpa only [sphereSobolevShiftedDegreeL_one_eq_degree] using norm_sphereSobolevShiftedDegreeL_le_two 1
  have hM (i : I) : ‖scaledFrameLogRadius d.radius d.frame i y • sphereSobolevDegreeL‖ ≤ 2*ε := by
    have ht := hd.scaled_frame_logRadius_small hf hy i
    change |scaledFrameLogRadius d.radius d.frame i y| ≤ ε/floor at ht
    have htε := ht.trans (div_le_self hε hf)
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul htε hD (norm_nonneg _) hε).trans_eq (by ring)
  exact (norm_firstCorrectionMatrixCrossL_le d
    (fun i x => scaledFrameLogRadius d.radius d.frame i x • sphereSobolevDegreeL) _ y hB hCA hC0
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1) hM hF0 hF1).trans_eq (by
      dsimp only [C0,C1];ring)

lemma Admissible.contDiffOn_principalDegreeCorrectionCrossL {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (principalDegreeCorrectionCrossL d) Y := by
  have ht (i : I) : ContDiffOn ℝ ∞ (scaledFrameLogRadius d.radius d.frame i) Y :=
    contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
      (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
      (fun j => (hd.1.2.2.2.2.2.2.1 j).mono (fun _x hx => hd.2.1.center_mem hx)) i
  exact hd.contDiffOn_firstCorrectionMatrixCrossL hY hΩ hK _ _
    (fun i => (ht i).smul contDiffOn_const)
    (fun i j => hd.contDiffOn_framePrincipalCoefficient (fun _x hx => hd.2.1.center_mem hx) hK i j)

/-- Exact r*f degree/F group from the complete physical adjoint product. -/
lemma principalDegreeCorrectionCrossL_actual (d : Data) (y : X) (u : SphereSobolev 1) :
    (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
      ((d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) •
          sphereSobolevDegreeL (firstFrameAdjointCorrectionSobolevL d y j u)+
        (d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) •
          firstFrameAdjointCorrectionL d y i (sphereSobolevDegreeL u)))=
      principalDegreeCorrectionCrossL d y u := by
  simp only [principalDegreeCorrectionCrossL,firstCorrectionMatrixCrossL,_root_.sum_apply,
    _root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,scaledFrameLogRadius,map_smul]
end ShrinkingSpheres
