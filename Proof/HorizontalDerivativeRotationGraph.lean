import Proof.RelativeHorizontalAngularCommutation
import Proof.ActualCovariantRotationGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Differentiate the genuine rotation graph along an orthonormal curve
with horizontal first tangent. No unbounded angular operator is treated
as a bounded endomorphism on a single Sobolev space. -/
theorem horizontal_derivative_normalized_rotation_graph
    {D : Set NormalFrameRelativeParameter} {U : Set X}
    (hU : IsOpen U) {K : ℝ} {g : MetricField}
    (h : Elliptic U K g) (hK : 0 < K) (r : X → ℝ)
    (hD : IsOpen D) (hDsub : D ⊆ normalFrameRelativePositiveDomain U)
    (p : NormalFrameRelativeParameter) (hp : p ∈ D)
    (he : ∀ i j, metricPair g p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j)) =
      if i=j then 1 else 0) (a : X)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hF : ContDiffAt ℝ ∞ F p)
    (hX : DifferentiableAt ℝ (normalFrameRelativeHorizontalField g r a) p)
    (i j : I)
    (hGraph : ∀ q ∈ D,
      (∀ k l, metricPair g q.1.1 (q.1.2 (axis k)) (q.1.2 (axis l)) =
        if k=l then 1 else 0) → ∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F q (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative g F i j q
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+F q (sphereSobolevRotationL 2 i j u)))
    (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j
        (fderiv ℝ F p (normalFrameRelativeHorizontalField g r a p)
          (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative g
          (fun q => fderiv ℝ F q (normalFrameRelativeHorizontalField g r a q)) i j p
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          fderiv ℝ F p (normalFrameRelativeHorizontalField g r a p)
            (sphereSobolevRotationL 2 i j u)) := by
  let V := normalFrameRelativeHorizontalField g r a
  let c : ℝ → NormalFrameRelativeParameter := fun t => normalFrameRelativeNormalization g (p+t • V p)
  have hNp := normalFrameRelativeNormalization_eq_self g p he
  have hc0 : c 0=p := by simp only [c,zero_smul,add_zero,hNp]
  have hc : HasDerivAt c (V p) 0 :=
    hasDerivAt_relativeNormalization_horizontal_curve hU h hK r p (hDsub hp).1 he a
  have hLine := (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const (V p))
  change HasDerivAt (fun t : ℝ => p+t • V p) _ 0 at hLine
  simp only [one_smul,zero_add] at hLine
  have hLineTo : Tendsto (fun t : ℝ => p+t • V p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_smul,add_zero] using hLine.continuousAt.tendsto
  have hcTo : Tendsto c (𝓝 0) (𝓝 p) := by
    simpa only [hc0] using hc.continuousAt.tendsto
  have hPos : ∀ᶠ t in 𝓝 (0:ℝ),p+t • V p ∈ normalFrameRelativePositiveDomain U :=
    hLineTo.eventually ((isOpen_normalFrameRelativePositiveDomain hU).mem_nhds (hDsub hp))
  have hcD : ∀ᶠ t in 𝓝 (0:ℝ),c t ∈ D := hcTo.eventually (hD.mem_nhds hp)
  have hN : ContDiffAt ℝ ∞ (normalFrameRelativeNormalization g) p :=
    (h.contDiffOn_normalFrameRelativeNormalization hU hK).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hU).mem_nhds (hDsub hp))
  have hDF : ContDiffAt ℝ ∞ (fderiv ℝ F) p := hF.fderiv_right (m:=∞) (by simp)
  have hDFN : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F (normalFrameRelativeNormalization g q)) p := by
    apply ContDiffAt.comp p _ hN
    simpa only [hNp] using hDF
  have hJN : ContDiffAt ℝ ∞ (fun q => relativeRightRotationL i j
      (normalFrameRelativeNormalization g q)) p := (relativeRightRotationL i j).contDiff.contDiffAt.comp p hN
  have hA : DifferentiableAt ℝ (normalFrameRelativeAngularDerivative g F i j) p := by
    exact (hDFN.clm_apply hJN).differentiableAt (by simp)
  have hAtF : HasFDerivAt F (fderiv ℝ F p) (c 0) := by
    rw [hc0]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  have hAtA : HasFDerivAt (normalFrameRelativeAngularDerivative g F i j)
      (fderiv ℝ (normalFrameRelativeAngularDerivative g F i j) p) (c 0) := by
    rw [hc0]
    exact hA.hasFDerivAt
  have hFc := hAtF.comp_hasDerivAt 0 hc
  have hAc := hAtA.comp_hasDerivAt 0 hc
  have hLeft := (sphereSobolevRotationL 0 i j).hasFDerivAt.comp_hasDerivAt 0
    (hFc.clm_apply (hasDerivAt_const (0:ℝ) (sphereSobolevInclusionL 2 1 (by norm_num) u)))
  have hRight := (sphereSobolevInclusionL 0 (-1) (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
    ((hAc.clm_apply (hasDerivAt_const (0:ℝ) (sphereSobolevInclusionL 2 1 (by norm_num) u))).add
      (hFc.clm_apply (hasDerivAt_const (0:ℝ) (sphereSobolevRotationL 2 i j u))))
  have hEq : (fun t => sphereSobolevRotationL 0 i j
      (F (c t) (sphereSobolevInclusionL 2 1 (by norm_num) u))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative g F i j (c t)
          (sphereSobolevInclusionL 2 1 (by norm_num) u)+F (c t) (sphereSobolevRotationL 2 i j u))) := by
    filter_upwards [hPos,hcD] with t ht htD
    exact hGraph (c t) htD (h.normalFrameRelativeNormalization_orthonormal hK _ ht) u
  have hSame := hEq.deriv_eq
  have hLd := hLeft.deriv
  have hRd := hRight.deriv
  simp only [Function.comp_def,Pi.add_apply,map_zero,add_zero] at hLd hRd
  rw [hLd,hRd] at hSame
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,zero_add,V,
    fderiv_relative_angular_horizontal_commute hU h hK r p (hDsub hp) he a i j F hF hX] using hSame

end ShrinkingSpheres
