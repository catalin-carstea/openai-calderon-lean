import Proof.FirstCorrectionMatrixCross
import Proof.ActualCorrectionProductBudget
import Proof.FirstCorrectionCrossRemainder
import Proof.FramedFlatRaisingSobolev
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def principalRaisingCorrectionCrossL (d : Data) (x : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  firstCorrectionMatrixCrossL d (fun i _x => flatRaisingSobolevL 1 i)
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

def principalRaisingCorrectionPerturbationL (d : Data) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  firstCorrectionMatrixCrossL d (fun i _x => flatRaisingSobolevL 1 i)
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j-(if i=j then 1 else 0)) x

lemma firstCorrectionCrossRemainderL_eq_diagonal (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X) :
    firstCorrectionCrossRemainderL Q d y=
      firstCorrectionMatrixCrossL d (fun i _x => flatRaisingSobolevL 1 i)
        (fun _x i j => if i=j then 1 else 0) y := by
  simp only [firstCorrectionMatrixCrossL_delta,firstCorrectionCrossRemainderL,
    flatRaisingSobolevL_one Q hQ]

/-- Removing the SAME canonical J leaves precisely the h/F/raising matrix. -/
lemma principalRaisingCorrectionCrossL_sub_J (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X) :
    principalRaisingCorrectionCrossL d y-firstCorrectionCrossRemainderL Q d y=
      principalRaisingCorrectionPerturbationL d y := by
  rw [firstCorrectionCrossRemainderL_eq_diagonal Q hQ]
  exact firstCorrectionMatrixCrossL_sub d (fun i _x => flatRaisingSobolevL 1 i) _ _ y

lemma Admissible.norm_principalRaisingCorrectionPerturbationL_small {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖principalRaisingCorrectionPerturbationL d y‖ ≤
      162*K^2*(firstCorrectionGradeBound 1 K (M ⟨1,by omega⟩)+
        firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩))*ε := by
  let C0 := firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩)
  let C1 := firstCorrectionGradeBound 1 K (M ⟨1,by omega⟩)
  have hC0 : 0 ≤ C0 := firstCorrectionGradeBound_nonneg 0 K _
  have hC1 : 0 ≤ C1 := firstCorrectionGradeBound_nonneg 1 K _
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hr1 : d.radius y ≤ 1 := ((radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hB : 0 ≤ 9*K^2*ε*d.radius y := by positivity
  have hF0 (i : I) : ‖firstFrameAdjointCorrectionL d y i‖ ≤ C0 := by
    rw [← firstFrameAdjointCorrectionAtL_zero]
    exact hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 0 hy i
  have hF1 (i : I) : ‖firstFrameAdjointCorrectionSobolevL d y i‖ ≤ C1 :=
    hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 1 hy i
  have hA (i : I) : ‖flatRaisingSobolevL 1 i‖ ≤ 2 := norm_flatRaisingSobolevL_one_le_two i
  have hNorm := norm_firstCorrectionMatrixCrossL_le d (fun i _x => flatRaisingSobolevL 1 i)
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j-(if i=j then 1 else 0)) y
    hB (by norm_num : (0:ℝ) ≤ 2) hC0
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).1) hA hF0 hF1
  change ‖firstCorrectionMatrixCrossL d _ _ y‖ ≤ _
  calc
    _ ≤ 9*(9*K^2*ε*d.radius y)*2*(C1+C0) := hNorm
    _ = (162*K^2*(C1+C0)*ε)*d.radius y := by ring
    _ ≤ (162*K^2*(C1+C0)*ε)*1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
    _ = _ := by dsimp only [C0,C1];ring

lemma Admissible.contDiffOn_principalRaisingCorrectionPerturbationL {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (principalRaisingCorrectionPerturbationL d) Y :=
  hd.contDiffOn_firstCorrectionMatrixCrossL hY hΩ hK _ _ (fun _i => contDiffOn_const)
    (fun i j => (hd.contDiffOn_framePrincipalCoefficient (fun _x hx => hd.2.1.center_mem hx) hK i j).sub
      contDiffOn_const)
end ShrinkingSpheres
