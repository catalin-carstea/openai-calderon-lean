import Proof.NormalFrameRadialAffineModelGerms
import Proof.NormalFrameFirstModelFamily
import Proof.NormalFrameNormalizationDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

abbrev NormalFrameRelativeParameter := (X × (X →L[ℝ] X)) × ℝ

/-- Exchange the relative-radius and spatial coordinates without changing
    their product norm. -/
def normalFrameRelativeReorderL :
    (NormalFrameRelativeParameter × X) →L[ℝ] (NormalFrameSpatialParameter × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun q => ((q.1.1,q.2),q.1.2)
      map_add' := by intro a b;rfl
      map_smul' := by intro c a;rfl }
    1 (by
      intro q
      change ‖((q.1.1,q.2),q.1.2)‖ ≤ 1*‖q‖
      have hA : ‖q.1.1‖ ≤ ‖q‖ := (norm_fst_le q.1).trans (norm_fst_le q)
      have hT : ‖q.1.2‖ ≤ ‖q‖ := (norm_snd_le q.1).trans (norm_fst_le q)
      have hZ : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
      simpa only [Prod.norm_def,one_mul] using max_le (max_le hA hZ) hT)

lemma norm_normalFrameRelativeReorderL_le_one : ‖normalFrameRelativeReorderL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def normalFrameRelativeInput (r0 : ℝ) (q : NormalFrameRelativeParameter × X) :
    NormalFrameParameter × X :=
  ((q.1.1.1,((1+q.1.2)*r0,q.1.1.2)),q.2)

lemma contDiff_normalFrameRelativeInput (r0 : ℝ) : ContDiff ℝ ∞ (normalFrameRelativeInput r0) :=
  ((contDiff_fst.fst.fst).prodMk
    (((contDiff_const.add contDiff_fst.snd).mul contDiff_const).prodMk contDiff_fst.fst.snd)).prodMk contDiff_snd

def normalFrameRelativeCoefficient (g g₁ : MetricField) (E : X × X → X) (r0 : ℝ) :
    NormalFrameRelativeParameter × X → Mat :=
  orthonormalNormalFrameCoefficient g g₁ E ∘ normalFrameRelativeInput r0

def normalFrameRelativeFirstCovector (g g₁ : MetricField) (p : NormalFrameRelativeParameter) : X →L[ℝ] ℝ :=
  (1+p.2) • normalFrameFirstCovector g g₁ (normalizedOrthonormalFrameParameter g (p.1.1,(0,p.1.2)))

def normalFrameRelativeFirstModel (g g₁ : MetricField) (q : NormalFrameRelativeParameter × X) : Mat :=
  (1+q.1.2) • normalFrameRadialFirstModel g g₁ (q.1.1,q.2)

lemma normalFrameRelativeFirstModel_scalar (g g₁ : MetricField) (q : NormalFrameRelativeParameter × X) :
    normalFrameRelativeFirstModel g g₁ q = normalFrameRelativeFirstCovector g g₁ q.1 q.2 • (1:Mat) := by
  simp only [normalFrameRelativeFirstModel,normalFrameRelativeFirstCovector,normalFrameRadialFirstModel,
    orthonormalFirstRadialModel,ContinuousLinearMap.smul_apply,smul_smul,smul_eq_mul]

lemma normalFrameRelativeCoefficient_radial (g g₁ : MetricField) (E : X × X → X) (r0 : ℝ)
    (q : NormalFrameRelativeParameter × X) :
    normalFrameRelativeCoefficient g g₁ E r0 q =
      normalFrameRadialCoefficient g g₁ E ((q.1.1,q.2),(1+q.1.2)*r0) := rfl

lemma normalFrameRelativeCoefficient_affine_residual (g g₁ : MetricField) (E : X × X → X) (r0 : ℝ)
    (q : NormalFrameRelativeParameter × X) :
    normalFrameRelativeCoefficient g g₁ E r0 q-(1:Mat)-r0 • normalFrameRelativeFirstModel g g₁ q =
      normalFrameRadialRemainder g g₁ E ((q.1.1,q.2),(1+q.1.2)*r0) := by
  rw [normalFrameRadialRemainder_apply,normalFrameRelativeCoefficient_radial]
  simp only [normalFrameRelativeFirstModel,smul_smul,mul_comm r0]

def normalFrameRelativePositiveDomain (Ω : Set X) : Set NormalFrameRelativeParameter :=
  (fun p : NormalFrameRelativeParameter => (p.1.1,((0:ℝ),p.1.2))) ⁻¹' normalFramePositiveDomain Ω

lemma contDiff_normalFrameRelativeZeroInput :
    ContDiff ℝ ∞ (fun p : NormalFrameRelativeParameter => (p.1.1,((0:ℝ),p.1.2))) :=
  contDiff_fst.fst.prodMk (contDiff_const.prodMk contDiff_fst.snd)

lemma isOpen_normalFrameRelativePositiveDomain {Ω : Set X} (hΩ : IsOpen Ω) :
    IsOpen (normalFrameRelativePositiveDomain Ω) :=
  (isOpen_normalFramePositiveDomain hΩ).preimage contDiff_normalFrameRelativeZeroInput.continuous

end ShrinkingSpheres
