import Proof.NormalFrameNormalizationParallelJet
import Proof.NormalFrameHorizontalRescaling
import Proof.NormalFrameRelativeNormalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The orthonormal retraction preserves the horizontal first tangent. The
relative radius component is independent and is preserved exactly. -/
theorem hasDerivAt_relativeNormalization_horizontal_curve
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (r : X → ℝ)
    (p : NormalFrameRelativeParameter) (hp : p.1.1 ∈ Ω)
    (he : ∀ i j, metricPair g p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j)) =
      if i=j then 1 else 0) (a : X) :
    HasDerivAt (fun t : ℝ => normalFrameRelativeNormalization g
      (p+t • normalFrameRelativeHorizontalField g r a p))
      (normalFrameRelativeHorizontalField g r a p) 0 := by
  let e : Frame := fun _ i => p.1.2 (axis i)
  have hL : frameVectorLinear e p.1.1 = p.1.2 := by
    apply ContinuousLinearMap.ext
    intro u
    rw [frameVectorLinear_apply]
    exact frameVector_linear_axes p.1.2 p.1.1 u
  have hN := hasDerivAt_normalFrameNormalizedLinear_parallel hΩ h hK e
    (fun _ => (0:ℝ)) hp he a
  have hN' : HasDerivAt (fun t : ℝ => normalFrameNormalizedLinear g
      (normalFrameRelativeZeroL (p+t • normalFrameRelativeHorizontalField g r a p)))
      (-((connectionBilinear g p.1.1 a).comp p.1.2)) 0 := by
    have hCurve : (fun t : ℝ => normalFrameRelativeZeroL
        (p+t • normalFrameRelativeHorizontalField g r a p)) =
        normalFrameParallelCurve g e (fun _ => (0:ℝ)) p.1.1 a := by
      funext t
      unfold normalFrameParallelCurve
      rw [hL]
      change (p.1.1+t • a,(0,p.1.2+t • (-((connectionBilinear g p.1.1 a).comp p.1.2)))) =
        (p.1.1+t • a,(0,p.1.2-t • ((connectionBilinear g p.1.1 a).comp p.1.2)))
      simp only [smul_neg,sub_eq_add_neg]
    change HasDerivAt ((normalFrameNormalizedLinear g) ∘ (fun t : ℝ =>
      normalFrameRelativeZeroL (p+t • normalFrameRelativeHorizontalField g r a p))) _ 0
    rw [hCurve]
    simpa only [Function.comp_def,hL] using hN
  have hCenter : HasDerivAt (fun t : ℝ => p.1.1+t • a) a 0 := by
    have hc :=
      (hasDerivAt_const (0:ℝ) p.1.1).add ((hasDerivAt_id (0:ℝ)).smul_const a)
    change HasDerivAt (fun t : ℝ => p.1.1+t • a) _ 0 at hc
    simpa only [one_smul,zero_add] using hc
  have hRadius : HasDerivAt (fun t : ℝ => p.2+t*((1+p.2)*
      fderiv ℝ (fun x => Real.log (r x)) p.1.1 a))
      ((1+p.2)*fderiv ℝ (fun x => Real.log (r x)) p.1.1 a) 0 := by
    have hc :=
      (hasDerivAt_const (0:ℝ) p.2).add
        ((hasDerivAt_id (0:ℝ)).mul_const ((1+p.2)*
          fderiv ℝ (fun x => Real.log (r x)) p.1.1 a))
    change HasDerivAt (fun t : ℝ => p.2+t*((1+p.2)*
      fderiv ℝ (fun x => Real.log (r x)) p.1.1 a)) _ 0 at hc
    simpa only [one_mul,zero_add] using hc
  exact (hCenter.prodMk hN').prodMk hRadius

theorem fderiv_relativeNormalization_horizontal
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (r : X → ℝ)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j, metricPair g p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j)) =
      if i=j then 1 else 0) (a : X) :
    fderiv ℝ (normalFrameRelativeNormalization g) p
      (normalFrameRelativeHorizontalField g r a p) =
        normalFrameRelativeHorizontalField g r a p := by
  have hDiff := ((h.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hp)).differentiableAt (by simp)
  have hLine : HasDerivAt (fun t : ℝ => p+t • normalFrameRelativeHorizontalField g r a p)
      (normalFrameRelativeHorizontalField g r a p) 0 := by
    have hc :=
      (hasDerivAt_const (0:ℝ) p).add
        ((hasDerivAt_id (0:ℝ)).smul_const (normalFrameRelativeHorizontalField g r a p))
    change HasDerivAt (fun t : ℝ => p+t • normalFrameRelativeHorizontalField g r a p) _ 0 at hc
    simpa only [one_smul,zero_add] using hc
  have hAt : HasFDerivAt (normalFrameRelativeNormalization g)
      (fderiv ℝ (normalFrameRelativeNormalization g) p)
      (p+(0:ℝ) • normalFrameRelativeHorizontalField g r a p) := by
    simpa only [zero_smul,add_zero] using hDiff.hasFDerivAt
  have hc := hAt.comp_hasDerivAt 0 hLine
  change HasDerivAt (fun t : ℝ => normalFrameRelativeNormalization g
    (p+t • normalFrameRelativeHorizontalField g r a p)) _ 0 at hc
  exact hc.unique
    (hasDerivAt_relativeNormalization_horizontal_curve hΩ h hK r p hp.1 he a)

end ShrinkingSpheres
