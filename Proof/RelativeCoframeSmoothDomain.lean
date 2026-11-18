import Proof.NormalFrameRelativeNormalization
import Proof.NormalFrameRelativeCoframeGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma Elliptic.contDiffOn_relativeCoframeValue {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (a : X) (j : I) :
    ContDiffOn ℝ ∞ (normalFrameRelativeCoframeValue g a j) (normalFrameRelativePositiveDomain Ω) := by
  intro p hp
  let N := normalFrameRelativeNormalization g
  have hN : ContDiffAt ℝ ∞ N p := (h.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hp)
  have hFrame : ContDiffAt ℝ ∞ (fun q => (N q).1.2 (axis j)) p := hN.fst.snd.clm_apply contDiffAt_const
  have hMetric (i k : I) : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter => g q.1.1 i k) p :=
    ((h.1 i k).contDiffAt (hΩ.mem_nhds hp.1)).comp p contDiffAt_fst.fst
  have hCoord (k : I) : ContDiffAt ℝ ∞ (fun q => ((N q).1.2 (axis j)) k) p :=
    (EuclideanSpace.proj (𝕜:=ℝ) k).contDiff.contDiffAt.comp p hFrame
  have hh : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter =>
      ∑ i : I,∑ k : I,g q.1.1 i k*a i*((N q).1.2 (axis j)) k) p := ContDiffAt.sum (fun i (_hi : i ∈ Finset.univ) =>
    ContDiffAt.sum (fun k (_hk : k ∈ Finset.univ) => ((hMetric i k).mul contDiffAt_const).mul (hCoord k)))
  exact hh.contDiffWithinAt
end ShrinkingSpheres
