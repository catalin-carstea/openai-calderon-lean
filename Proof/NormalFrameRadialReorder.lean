import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

abbrev NormalFrameSpatialParameter := (X × (X →L[ℝ] X)) × X

/-- Put the independent radius last, keeping center, frame and spatial
    variables together as the parameter differentiated by Taylor. -/
def normalFrameRadialReorderL : (NormalFrameSpatialParameter × ℝ) →L[ℝ] (NormalFrameParameter × X) :=
  LinearMap.mkContinuous
    { toFun := fun q => ((q.1.1.1,(q.2,q.1.1.2)),q.1.2)
      map_add' := by intro a b;rfl
      map_smul' := by intro c a;rfl }
    1 (by
      intro q
      change ‖((q.1.1.1,(q.2,q.1.1.2)),q.1.2)‖ ≤ 1*‖q‖
      have hY : ‖q.1.1.1‖ ≤ ‖q‖ := (norm_fst_le q.1.1).trans ((norm_fst_le q.1).trans (norm_fst_le q))
      have hR : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
      have hL : ‖q.1.1.2‖ ≤ ‖q‖ := (norm_snd_le q.1.1).trans ((norm_fst_le q.1).trans (norm_fst_le q))
      have hZ : ‖q.1.2‖ ≤ ‖q‖ := (norm_snd_le q.1).trans (norm_fst_le q)
      simpa only [Prod.norm_def,one_mul] using max_le (max_le hY (max_le hR hL)) hZ)

lemma normalFrameRadialReorderL_apply (q : NormalFrameSpatialParameter × ℝ) :
    normalFrameRadialReorderL q = ((q.1.1.1,(q.2,q.1.1.2)),q.1.2) := rfl

lemma norm_normalFrameRadialReorderL_le_one : ‖normalFrameRadialReorderL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def normalFrameRadialCoefficient (g g₁ : MetricField) (E : X × X → X) :
    NormalFrameSpatialParameter × ℝ → Mat :=
  orthonormalNormalFrameCoefficient g g₁ E ∘ normalFrameRadialReorderL

lemma normalFrameRadialCoefficient_apply (g g₁ : MetricField) (E : X × X → X)
    (p : NormalFrameSpatialParameter) (s : ℝ) :
    normalFrameRadialCoefficient g g₁ E (p,s) =
      orthonormalNormalFrameCoefficient g g₁ E ((p.1.1,(s,p.1.2)),p.2) := rfl

end ShrinkingSpheres
