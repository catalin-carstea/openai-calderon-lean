import Proof.FrameCovariantCurvatureComm

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

lemma contDiffOn_threeRotationBracket {Y : Set X} (p q : X → I → ℝ)
    (hp : ContDiffOn ℝ ∞ p Y) (hq : ContDiffOn ℝ ∞ q Y) :
    ContDiffOn ℝ ∞ (fun x => threeRotationBracket (p x) (q x)) Y := by
  apply contDiffOn_pi.mpr
  intro k
  have hP (i : I) := contDiffOn_pi.mp hp i
  have hQ (i : I) := contDiffOn_pi.mp hq i
  by_cases h0 : k=0
  · simpa [threeRotationBracket,h0] using ((hP 2).mul (hQ 1)).sub ((hP 1).mul (hQ 2))
  · by_cases h1 : k=1
    · simpa [threeRotationBracket,h0,h1]
        using ((hP 0).mul (hQ 2)).sub ((hP 2).mul (hQ 0))
    · simpa [threeRotationBracket,h0,h1]
        using ((hP 1).mul (hQ 0)).sub ((hP 0).mul (hQ 1))

lemma contDiffOn_threeConnectionCurvature {Y : Set X} (hY : IsOpen Y)
    (C : X → X →L[ℝ] (I → ℝ)) (hC : ContDiffOn ℝ ∞ C Y) (a b : X) :
    ContDiffOn ℝ ∞ (fun x => threeConnectionCurvature C x a b) Y := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ C) Y := hC.fderiv_of_isOpen hY (by simp)
  have hDab := (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => a) Y)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => b) Y)
  have hDba := (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => b) Y)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => a) Y)
  have hp : ContDiffOn ℝ ∞ (fun x => C x a) Y := hC.clm_apply contDiffOn_const
  have hq : ContDiffOn ℝ ∞ (fun x => C x b) Y := hC.clm_apply contDiffOn_const
  exact (hDab.sub hDba).sub (contDiffOn_threeRotationBracket _ _ hp hq)

/-- The SAME physical curvature coefficient is smooth as a bounded
operator at every genuine Sobolev grade. No quantitative frame jets enter. -/
theorem Elliptic.contDiffOn_frameCurvatureSobolevL {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    (s : ℝ) (a b : X) :
    ContDiffOn ℝ ∞ (fun x => frameCurvatureSobolevL s g e x a b) Y := by
  have hC := hg.contDiffOn_frameConnectionThreeLinear hY hK e he
  have hKappa := contDiffOn_threeConnectionCurvature hY _ hC a b
  have hOp : ContDiffOn ℝ ∞ (fun x => -threeRotationL s
      (threeConnectionCurvature (frameConnectionThreeLinear g e) x a b)) Y := by
    simpa only [Function.comp_def,threeRotationMapL_apply] using
      ((threeRotationMapL s).contDiff.comp_contDiffOn hKappa).neg
  apply hOp.congr
  intro x hx
  rw [hg.frameConnectionThreeLinear_curvature hY hK e he hFrame hx a b]
  rfl

end ShrinkingSpheres
