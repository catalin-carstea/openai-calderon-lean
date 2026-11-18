import Proof.RelativeNormalCoefficientSymmetryDomain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

def strictNormalDiskTube (Y : Set X) (g : MetricField) (R : X → ℝ) : Set (X × X) :=
  {q | q.1 ∈ Y ∧ metricPair g q.1 q.2 q.2 < (R q.1)^2}
lemma isOpen_strictNormalDiskTube {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (R : X → ℝ) (hR : ContinuousOn R Y) :
    IsOpen (strictNormalDiskTube Y g R) := by
  have hG (i j : I) : ContDiffOn ℝ ∞ (fun q : X × X => g q.1 i j) (Y ×ˢ (univ:Set X)) :=
    (hg.1 i j).comp contDiffOn_fst (fun q hq => hSub hq.1)
  have hV (i : I) : ContDiff ℝ ∞ (fun q : X × X => q.2 i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd
  have hPair : ContinuousOn (fun q : X × X => metricPair g q.1 q.2 q.2) (Y ×ˢ (univ:Set X)) :=
    (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ((hG i j).mul (hV i).contDiffOn).mul (hV j).contDiffOn))).continuousOn
  have hRadius : ContinuousOn (fun q : X × X => R q.1) (Y ×ˢ (univ:Set X)) :=
    hR.comp continuousOn_fst (fun q hq => hq.1)
  have hOpen := (hPair.sub (hRadius.pow 2)).isOpen_inter_preimage (hY.prod isOpen_univ) (isOpen_Iio (a:=(0:ℝ)))
  convert hOpen using 1
  ext q
  simp only [strictNormalDiskTube,mem_ofPred_eq,mem_inter_iff,mem_prod,mem_univ,and_true,mem_preimage,mem_Iio,Pi.sub_apply,Pi.pow_apply,sub_neg]

lemma Elliptic.contDiffOn_relative_geometric_input {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (r : ℝ) :
    ContDiffOn ℝ ∞ (normalFrameRelativeGeometricInput g r)
      (normalFrameRelativePositiveDomain Ω ×ˢ (univ:Set X)) := by
  have hN := hg.contDiffOn_normalFrameRelativeNormalization hΩ hK
  intro q hq
  have hNorm := hN.contDiffAt ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hq.1)
  have hInput := (contDiff_normalFrameRelativeInput r).contDiffAt.comp q
    ((hNorm.comp q contDiffAt_fst).prodMk contDiffAt_snd)
  exact (contDiff_normalFrameInput.contDiffAt.comp q hInput).contDiffWithinAt
end ShrinkingSpheres
