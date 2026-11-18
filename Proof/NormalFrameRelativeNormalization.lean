import Proof.NormalFrameRelativeCoframeGeometry
import Proof.UniformNormalFrameNormalizationJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- A smooth retraction to genuine orthonormal frame parameters. The
    independent relative-radius coordinate is preserved exactly. -/
def normalFrameRelativeNormalization (g : MetricField) (p : NormalFrameRelativeParameter) :
    NormalFrameRelativeParameter :=
  ((p.1.1,normalFrameNormalizedLinear g (normalFrameRelativeZeroL p)),p.2)

lemma normalFrameRelativeNormalization_eq_self (g : MetricField) (p : NormalFrameRelativeParameter)
    (he : ∀ i j,metricPair g p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j)) = if i=j then 1 else 0) :
    normalFrameRelativeNormalization g p = p := by
  have h := normalFrameNormalizedLinear_eq_self g (normalFrameRelativeZeroL p) he
  change ((p.1.1,normalFrameNormalizedLinear g (normalFrameRelativeZeroL p)),p.2) = p
  rw [h]
  rfl

theorem Elliptic.normalFrameRelativeNormalization_orthonormal {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (p : NormalFrameRelativeParameter)
    (hp : p ∈ normalFrameRelativePositiveDomain Ω) :
    ∀ i j,metricPair g p.1.1 ((normalFrameRelativeNormalization g p).1.2 (axis i))
      ((normalFrameRelativeNormalization g p).1.2 (axis j)) = if i=j then 1 else 0 := by
  exact normalFrameNormalizedLinear_orthonormal g (normalFrameRelativeZeroL p)
    (fun u v => metricPair_symm g p.1.1 (p.1.2 u) (p.1.2 v) (h.2 p.1.1 hp.1).1)
    (h.normalFramePositiveDomain_pair_positive hK hp)

lemma Elliptic.normalFrameRelativeNormalization_mem {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (p : NormalFrameRelativeParameter)
    (hp : p ∈ normalFrameRelativePositiveDomain Ω) :
    normalFrameRelativeNormalization g p ∈ normalFrameRelativePositiveDomain Ω := by
  exact normalFramePositiveDomain_mem_of_orthonormal g
    (normalFrameRelativeZeroL (normalFrameRelativeNormalization g p)) hp.1
    (h.normalFrameRelativeNormalization_orthonormal hK p hp)

lemma Elliptic.normalFrameRelativeNormalization_idempotent {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (p : NormalFrameRelativeParameter)
    (hp : p ∈ normalFrameRelativePositiveDomain Ω) :
    normalFrameRelativeNormalization g (normalFrameRelativeNormalization g p) =
      normalFrameRelativeNormalization g p :=
  normalFrameRelativeNormalization_eq_self g _ (h.normalFrameRelativeNormalization_orthonormal hK p hp)

theorem Elliptic.contDiffOn_normalFrameRelativeNormalization {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (normalFrameRelativeNormalization g) (normalFrameRelativePositiveDomain Ω) := by
  intro p hp
  have hSmooth := (h.normalFrame_normalization_open_domain hΩ hK).2.1.contDiffAt
    ((isOpen_normalFramePositiveDomain hΩ).mem_nhds hp)
  have hN : ContDiffAt ℝ ∞ (fun q => normalFrameNormalizedLinear g (normalFrameRelativeZeroL q)) p :=
    hSmooth.snd.snd.comp p normalFrameRelativeZeroL.contDiff.contDiffAt
  exact ((contDiffAt_fst.fst.prodMk hN).prodMk contDiffAt_snd).contDiffWithinAt

lemma normalFrameRelativeCoefficient_eq_raw_normalized (g g₁ : MetricField) (E : X × X → X)
    (r : ℝ) (p : NormalFrameRelativeParameter) (z : X) :
    normalFrameRelativeCoefficient g g₁ E r (p,z) =
      normalFrameNormalizedCoefficient g g₁ E (normalFrameRelativeInput r
        (normalFrameRelativeNormalization g p,z)) := rfl

lemma Elliptic.normalFrameRelativeCoefficient_normalization {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (g₁ : MetricField) (E : X × X → X)
    (r : ℝ) (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) (z : X) :
    normalFrameRelativeCoefficient g g₁ E r (normalFrameRelativeNormalization g p,z) =
      normalFrameRelativeCoefficient g g₁ E r (p,z) := by
  rw [normalFrameRelativeCoefficient_eq_raw_normalized,normalFrameRelativeCoefficient_eq_raw_normalized,
    h.normalFrameRelativeNormalization_idempotent hK p hp]

end ShrinkingSpheres
