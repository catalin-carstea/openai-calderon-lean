import Proof.CoarseHorizontalCovariantGerm
import Proof.NativeFirstCovariantHalfLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Density of the genuine H1 inclusion fixes its strong half extension. -/
lemma coarse_half_extension_unique
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hT : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      T.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) : L=T := by
  exact clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) L T (hL.symm.trans hT)

/-- The SAME native inclusion square survives two ordered horizontal
parameter derivatives. No regularity is assigned to a pointwise jet choice. -/
lemma compatible_endpoint_second_horizontal
    {P V0 V1 W0 W1 : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V0] [NormedSpace ℝ V0]
    [NormedAddCommGroup V1] [NormedSpace ℝ V1]
    [NormedAddCommGroup W0] [NormedSpace ℝ W0]
    [NormedAddCommGroup W1] [NormedSpace ℝ W1]
    (F : P → V0 →L[ℝ] W0) (G : P → V1 →L[ℝ] W1)
    (Iout : W0 →L[ℝ] W1) (Iin : V0 →L[ℝ] V1)
    {D : Set P} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hG : ContDiffOn ℝ ∞ G D) (B : P → P) {p : P} (hp : p ∈ D)
    (hB : ContDiffAt ℝ ∞ B p)
    (hCompat : ∀ q ∈ D,Iout.comp (F q)=(G q).comp Iin) (c : P) :
    Iout.comp (fderiv ℝ (fun q => fderiv ℝ F q (B q)) p c)=
      (fderiv ℝ (fun q => fderiv ℝ G q (B q)) p c).comp Iin := by
  have hF' := ((hF.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB
  have hG' := ((hG.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB
  apply compatible_endpoint_fderiv _ _ Iout Iin p c
    (hF'.differentiableAt (by simp)) (hG'.differentiableAt (by simp))
  filter_upwards [hD.mem_nhds hp] with q hq
  apply compatible_endpoint_fderiv F G Iout Iin q (B q)
    ((hF.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp))
    ((hG.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp))
  filter_upwards [hD.mem_nhds hq] with r hr
  exact hCompat r hr

/-- A smooth native coarse germ determines the strong half first jet on
an entire neighborhood. The extension is fixed by a genuine dense graph. -/
lemma strong_half_native_horizontal_germ
    (d : Data) (r0 : ℝ) {y : X}
    (S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {D : Set NormalFrameRelativeParameter} (hD : IsOpen D)
    (hF : ContDiffOn ℝ ∞ F D) (hG : ContDiffOn ℝ ∞ G D)
    (B : NormalFrameRelativeParameter → NormalFrameRelativeParameter)
    (hQ : ContinuousAt (normalFrameRelativeActualParameter d r0) y)
    (hp : normalFrameRelativeActualParameter d r0 y ∈ D)
    (hS : S =ᶠ[𝓝 y] fun x => fderiv ℝ F (normalFrameRelativeActualParameter d r0 x)
      (B (normalFrameRelativeActualParameter d r0 x)))
    (hL : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S x)=
        (L x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hCompat : ∀ q ∈ D,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (F q)=
        (G q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    L =ᶠ[𝓝 y] fun x => fderiv ℝ G (normalFrameRelativeActualParameter d r0 x)
      (B (normalFrameRelativeActualParameter d r0 x)) := by
  filter_upwards [hQ.eventually (hD.mem_nhds hp),hS,hL] with x hx hSx hLx
  apply coarse_half_extension_unique (S x) (L x) _ hLx
  rw [hSx]
  apply compatible_endpoint_fderiv F G _ _ _ _
    ((hF.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp))
    ((hG.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp))
  filter_upwards [hD.mem_nhds hx] with q hq
  exact hCompat q hq

end ShrinkingSpheres.ParallelEnergy
