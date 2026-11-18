import Proof.PrincipalModelPotentialLinearCoarse
import Proof.FrameCorrectionErrorCoarseCross
import Proof.Curvature
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffOn_hessianBilinear_of_smooth {Y : Set X} {g : MetricField} {f : X → ℝ}
    (hY : IsOpen Y) (hf : ContDiffOn ℝ ∞ f Y)
    (hΓ : ContDiffOn ℝ ∞ (connectionBilinear g) Y) :
    ContDiffOn ℝ ∞ (hessianBilinear g f) Y := by
  have hD := hf.fderiv_of_isOpen (m:=∞) hY (by simp)
  have hDD := hD.fderiv_of_isOpen (m:=∞) hY (by simp)
  exact hDD.sub (((ContinuousLinearMap.compL ℝ X X ℝ).contDiff.comp_contDiffOn hD).clm_comp hΓ)

lemma Admissible.contDiffOn_principalModelPotentialLinearCoarseL {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (principalModelPotentialLinearCoarseL d) Y := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have he (i : I) := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hLog := hd.2.2.2.2.1.1.log (fun y hy => (hd.2.2.2.2.1.2 y hy).1.ne')
  have hH := contDiffOn_hessianBilinear_of_smooth hY hLog
    ((hd.1.1.contDiffOn_connectionBilinear hΩ hK).mono hSub)
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (hd.contDiffOn_framePrincipalCoefficient (fun _y hy => hd.2.1.center_mem hy) hK i j).smul
      ((hd.2.2.2.2.1.1.mul ((hH.clm_apply (he i)).clm_apply (he j))).smul contDiffOn_const)))

lemma Admissible.contDiffOn_frameCorrectionErrorCoarseCrossL {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ)
    (hE : ∀ i,ContDiffOn ℝ ∞ (E i) Y) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun y => Q y i j) Y) :
    ContDiffOn ℝ ∞ (frameCorrectionErrorCoarseCrossL d E Q) Y := by
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    (((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 0 i).clm_comp (hE j)).add
      ((hE i).clm_comp (hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 1 j)))))

lemma Admissible.contDiffOn_radiusFrameCorrectionErrorCoarseCrossL {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ)
    (hE : ∀ i,ContDiffOn ℝ ∞ (E i) Y) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun y => Q y i j) Y) :
    ContDiffOn ℝ ∞ (radiusFrameCorrectionErrorCoarseCrossL d E Q) Y :=
  hd.2.2.2.2.1.1.smul (hd.contDiffOn_frameCorrectionErrorCoarseCrossL hY hΩ hK E Q hE hQ)

lemma Admissible.norm_radiusFrameCorrectionErrorCoarseCrossL_small {Y Ω : Set X}
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε CE : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hΩ : IsOpen Ω) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCE : 0 ≤ CE)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) {y : X} (hy : y ∈ Y)
    (hE : ∀ i,‖E i y‖ ≤ CE*d.radius y) :
    ‖radiusFrameCorrectionErrorCoarseCrossL d E
      (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y‖ ≤
      81*(K+1)*K^2*(firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩)+
        firstCorrectionGradeBound 1 K (M ⟨1,by omega⟩))*CE*ε := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  exact (ShrinkingSpheres.norm_radiusFrameCorrectionErrorCoarseCrossL_small d E _ y (by positivity) hCE
    (firstCorrectionGradeBound_nonneg 0 K _) (firstCorrectionGradeBound_nonneg 1 K _)
    hr.le (hrε.trans hε1) hrε
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1) hE
    (fun i => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 0 hy i)
    (fun j => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 1 hy j)).trans_eq (by ring)
end ShrinkingSpheres
