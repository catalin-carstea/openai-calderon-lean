import Proof.PhysicalPotentialRemainderCoarse
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffOn_angularConnectionL {Y : Set X} (A : X → I → I → ℝ)
    (hA : ∀ i j,ContDiffOn ℝ ∞ (fun y => A y i j) Y) :
    ContDiffOn ℝ ∞ (fun y => angularConnectionL (A y)) Y :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (contDiffOn_const.mul (hA i j)).smul contDiffOn_const))

lemma Admissible.contDiffOn_firstFrameAdjointHorizontalCommutatorL {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i j : I) :
    ContDiffOn ℝ ∞ (fun y => firstFrameAdjointHorizontalCommutatorL d y (d.frame y i) j) Y := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have he (a : I) := hd.1.2.2.2.2.2.2.1 a
  have hΓ (a b : I) := (hd.1.1.contDiffOn_frameConnection hΩ hK d.frame he
    (fun y => d.frame y i) (he i) a b).mono hSub
  have hAng := contDiffOn_angularConnectionL _ hΓ
  have hF0 (a : I) := hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK a
  have hF1 := hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 1 j
  have hOrd := ((hF0 j).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply ((he i).mono hSub)
  change ContDiffOn ℝ ∞ (fun y =>
    (fderiv ℝ (fun x => firstFrameAdjointCorrectionL d x j) y (d.frame y i)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))+
    (angularConnectionL (frameConnectionCoefficient d.γ d.frame y (d.frame y i))).comp
      (firstFrameAdjointCorrectionSobolevL d y j)-
    (firstFrameAdjointCorrectionL d y j).comp
      (angularConnectionL (frameConnectionCoefficient d.γ d.frame y (d.frame y i)))-
    (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k • firstFrameAdjointCorrectionL d y k).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) Y
  exact (((hOrd.clm_comp contDiffOn_const).add (hAng.clm_comp hF1)).sub
    ((hF0 j).clm_comp hAng)).sub
      ((ContDiffOn.sum (fun k _ => (hΓ j k).smul (hF0 k))).clm_comp contDiffOn_const)

lemma Admissible.contDiffOn_principalCovariantPotentialL {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : ∀ i j,ContDiffOn ℝ ∞ (S i j) Y) :
    ContDiffOn ℝ ∞ (principalCovariantPotentialL d S) Y := by
  have hCross : ContDiffOn ℝ ∞ (fun y => d.radius y • (∑ i : I,∑ j : I,
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        (firstFrameAdjointHorizontalCommutatorL d y (d.frame y i) j+S i j y))) Y :=
    hd.2.2.2.2.1.1.smul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (hd.contDiffOn_framePrincipalCoefficient (fun _y hy => hd.2.1.center_mem hy) hK i j).smul
        ((hd.contDiffOn_firstFrameAdjointHorizontalCommutatorL hY hΩ hK i j).add (hS i j)))))
  apply hCross.congr
  intro y hy
  simp only [principalCovariantPotentialL,hd.firstFrameAdjointHorizontalCommutatorL_eq hY hΩ hK hy]

lemma PhysicalPrincipalData.potentialRemainderCoarseL_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ P.potentialRemainderCoarseL Y := by
  have hModel := hd.contDiffOn_principalModelPotentialLinearCoarseL hY hΩ hK
  have hCov := hd.contDiffOn_principalCovariantPotentialL hY hΩ hK P.tensor P.tensor_smooth
  have hRP := hd.contDiffOn_principalRaisingCorrectionPerturbationL hY hΩ hK
  have hDF := hd.contDiffOn_principalDegreeCorrectionCrossL hY hΩ hK
  have hFF := (hd.contDiffOn_principalCorrectionProductL hY hΩ hK 0).clm_comp
    (contDiffOn_const (c:=sphereSobolevInclusionL 1 0 (by norm_num)))
  have hFE := hd.contDiffOn_radiusFrameCorrectionErrorCoarseCrossL hY hΩ hK
    (actualFrameFirstAdjointErrorFamily d P.adjoint P.center) _
      (P.coarse_first_error_smooth hd hY hΩ (fun _y hy => hd.2.1.center_mem hy) hK)
      (fun i j => hd.contDiffOn_framePrincipalCoefficient (fun _y hy => hd.2.1.center_mem hy) hK i j)
  exact ((((hModel.add hCov).add hRP).add hDF).add hFF).add hFE
end ShrinkingSpheres
