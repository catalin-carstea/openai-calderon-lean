import Proof.NormalFrameRelativeActualCoefficientGerms
import Proof.CanonicalFirstRadialFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Actual center, frame and radius expressed in one fixed relative-radius chart. -/
def normalFrameRelativeActualParameter (d : Data) (r0 : ℝ) (x : X) : NormalFrameRelativeParameter :=
  ((x,frameVectorLinear d.frame x),d.radius x/r0-1)

lemma normalFrameRelativeActualParameter_point (d : Data) (y : X) (hr : d.radius y ≠ 0) :
    normalFrameRelativeActualParameter d (d.radius y) y = ((y,frameVectorLinear d.frame y),0) := by
  simp only [normalFrameRelativeActualParameter,div_self hr,sub_self]

lemma normalFrameRelativeActualParameter_input (d : Data) {r0 : ℝ} (hr : r0 ≠ 0) (x z : X) :
    normalFrameRelativeInput r0 (normalFrameRelativeActualParameter d r0 x,z) =
      ((x,(d.radius x,frameVectorLinear d.frame x)),z) := by
  have hh : (1+(d.radius x/r0-1))*r0 = d.radius x := by field_simp;ring
  change ((x,((1+(d.radius x/r0-1))*r0,frameVectorLinear d.frame x)),z) = _
  rw [hh]

lemma Background.normalFrameRelativeCoefficient_actual_parameter {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {x : X} (hx : x ∈ Ω)
    {r0 : ℝ} (hr : r0 ≠ 0) (z : X) :
    normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r0
      (normalFrameRelativeActualParameter d r0 x,z) = normalizedFirstNormalCoefficient d x z := by
  have he (i j : I) : metricPair d.γ x (frameVectorLinear d.frame x (axis i))
      (frameVectorLinear d.frame x (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 x hx i j
  rw [normalFrameRelativeCoefficient_orthonormal _ _ _ _ _ he,normalFrameRelativeActualParameter_input d hr]
  exact normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame x z (d.radius x)

lemma contDiffOn_normalFrameRelativeActualParameter {Y : Set X} (d : Data) (r0 : ℝ)
    (hr : ContDiffOn ℝ ∞ d.radius Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y) :
    ContDiffOn ℝ ∞ (normalFrameRelativeActualParameter d r0) Y :=
  (contDiffOn_id.prodMk (contDiffOn_frameVectorLinear d.frame he)).prodMk
    ((hr.div_const r0).sub contDiffOn_const)
end ShrinkingSpheres
