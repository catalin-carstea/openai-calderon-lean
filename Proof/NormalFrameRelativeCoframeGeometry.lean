import Proof.NormalFrameRelativeGeometry
import Proof.NormalFrameCoframeMultiplierModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def normalFrameRelativeZeroL : NormalFrameRelativeParameter →L[ℝ] NormalFrameParameter :=
  LinearMap.mkContinuous
    { toFun := fun p => (p.1.1,((0:ℝ),p.1.2))
      map_add' := by intro p q;ext <;> simp
      map_smul' := by intro c p;ext <;> simp }
    1 (by
      intro p
      change ‖(p.1.1,((0:ℝ),p.1.2))‖ ≤ 1*‖p‖
      have hCenter : ‖p.1.1‖ ≤ ‖p‖ := (norm_fst_le p.1).trans (norm_fst_le p)
      have hFrame : ‖p.1.2‖ ≤ ‖p‖ := (norm_snd_le p.1).trans (norm_fst_le p)
      simpa only [Prod.norm_def,norm_zero,one_mul] using max_le hCenter (max_le (norm_nonneg p) hFrame))

lemma norm_normalFrameRelativeZeroL_le_one : ‖normalFrameRelativeZeroL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def normalFrameRelativeCenterL : NormalFrameRelativeParameter →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))).comp normalFrameRelativeZeroL

lemma norm_normalFrameRelativeCenterL_le_one : ‖normalFrameRelativeCenterL‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (ContinuousLinearMap.norm_fst_le ℝ X (ℝ × (X →L[ℝ] X))) norm_normalFrameRelativeZeroL_le_one
      (norm_nonneg _) zero_le_one).trans_eq (mul_one _))

def normalFrameRelativeCoframeValue (g : MetricField) (v : X) (j : I) (p : NormalFrameRelativeParameter) : ℝ :=
  normalFrameCoframeValue g v j (normalizedOrthonormalFrameParameter g (normalFrameRelativeZeroL p))

lemma normalFrameRelativeCoframeValue_apply (g : MetricField) (v : X) (j : I) (p : NormalFrameRelativeParameter) :
    normalFrameRelativeCoframeValue g v j p =
      ∑ i : I,∑ k : I,g (normalFrameRelativeCenterL p) i k*v i*
        (normalFrameNormalizedLinear g (normalFrameRelativeZeroL p) (axis j)) k := rfl

lemma normalFrameRelativeCoframeValue_orthonormal (g : MetricField) (v : X) (j : I)
    (y : X) (L : X →L[ℝ] X)
    (he : ∀ i k,metricPair g y (L (axis i)) (L (axis k)) = if i=k then 1 else 0) :
    normalFrameRelativeCoframeValue g v j ((y,L),0) = metricPair g y v (L (axis j)) := by
  change normalFrameCoframeValue g v j (normalizedOrthonormalFrameParameter g (y,(0,L))) = _
  rw [normalizedOrthonormalFrameParameter_eq_self g (y,(0,L)) he]
  rfl

end ShrinkingSpheres
