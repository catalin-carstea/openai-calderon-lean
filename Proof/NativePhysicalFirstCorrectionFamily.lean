import Proof.NormalizedFirstCorrectionCovector
import Proof.PhysicalFirstCorrectionCoarseNormalForm
import Proof.RelativeCoframeSmoothDomain
import Proof.ActualCovariantRotationGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def nativeFirstCorrectionDomain (Y Ω : Set X) : Set NormalFrameRelativeParameter :=
  normalFrameRelativePositiveDomain Ω ∩ {p | p.1.1 ∈ Y}

lemma isOpen_nativeFirstCorrectionDomain {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) :
    IsOpen (nativeFirstCorrectionDomain Y Ω) :=
  (isOpen_normalFrameRelativePositiveDomain hΩ).inter (hY.preimage (continuous_fst.fst))

def nativePhysicalFirstCorrectionScalar (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) : ℝ :=
  r0*(1+p.2)*fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 b

def nativePhysicalFirstCorrectionFamily (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (firstRadialAdjointOperatorMapL (normalizedFirstCorrectionCovector d.γ d.g₁ p)).comp
      (relativeCoframeNormalSobolevL 1 d.γ b p)+
    nativePhysicalFirstCorrectionScalar d r0 b p •
      firstRadialAdjointOperatorMapL (normalizedFirstCorrectionCovector d.γ d.g₁ p)

lemma nativePhysicalFirstCorrectionScalar_actual_parameter (d : Data) (r0 : ℝ) (hr0 : r0 ≠ 0)
    (x b : X) (hr : DifferentiableAt ℝ d.radius x) (hrx : d.radius x ≠ 0) :
    nativePhysicalFirstCorrectionScalar d r0 b (normalFrameRelativeActualParameter d r0 x) =
      fderiv ℝ d.radius x b := by
  have hRadius : r0*(1+(d.radius x/r0-1))=d.radius x := by field_simp;ring
  change r0*(1+(d.radius x/r0-1))*fderiv ℝ (fun x => Real.log (d.radius x)) x b = _
  rw [hRadius,logRadius_derivative d.radius x b hr hrx]
  field_simp

lemma Admissible.nativePhysicalFirstCorrectionFamily_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (r0 : ℝ) (b : X) :
    ContDiffOn ℝ ∞ (nativePhysicalFirstCorrectionFamily d r0 b) (nativeFirstCorrectionDomain Y Ω) := by
  have hCov : ContDiffOn ℝ ∞ (normalizedFirstCorrectionCovector d.γ d.g₁)
      (nativeFirstCorrectionDomain Y Ω) :=
    (hd.1.normalizedFirstCorrectionCovector_smooth hΩ hK).mono inter_subset_left
  have hB : ContDiffOn ℝ ∞ (fun p => firstRadialAdjointOperatorMapL
      (normalizedFirstCorrectionCovector d.γ d.g₁ p)) (nativeFirstCorrectionDomain Y Ω) :=
    firstRadialAdjointOperatorMapL.contDiff.comp_contDiffOn hCov
  have hM : ContDiffOn ℝ ∞ (relativeCoframeNormalSobolevL 1 d.γ b) (nativeFirstCorrectionDomain Y Ω) :=
    (hd.1.1.contDiffOn_relativeCoframeNormalSobolevL hΩ hK 1 b).mono inter_subset_left
  have hLog := ((hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')).fderiv_of_isOpen
    (m:=∞) hY (by simp)).clm_apply (contDiffOn_const (c:=b))
  have hLog' : ContDiffOn ℝ ∞ (fun p : NormalFrameRelativeParameter =>
      fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 b) (nativeFirstCorrectionDomain Y Ω) :=
    hLog.comp contDiffOn_fst.fst (fun p hp => hp.2)
  have hScalar : ContDiffOn ℝ ∞ (nativePhysicalFirstCorrectionScalar d r0 b)
      (nativeFirstCorrectionDomain Y Ω) :=
    (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_snd)).mul hLog'
  exact (hB.clm_comp hM).add (hScalar.smul hB)

lemma Background.nativeFirstCorrectionDomain_actual_parameter {Y Ω : Set X}
    (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (r0 : ℝ) {x : X} (hx : x ∈ Y) :
    normalFrameRelativeActualParameter d r0 x ∈ nativeFirstCorrectionDomain Y Ω := by
  have hFrame (i j : I) : metricPair d.γ x (frameVectorLinear d.frame x (axis i))
      (frameVectorLinear d.frame x (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 x (hSub hx) i j
  exact ⟨normalFramePositiveDomain_mem_of_orthonormal d.γ _ (hSub hx) hFrame,hx⟩

theorem Admissible.nativePhysicalFirstCorrectionFamily_actual_germ {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (r0 : ℝ) (hr0 : r0 ≠ 0) {y : X} (hy : y ∈ Y) (b : X) :
    physicalFirstCorrectionCoarseFamily d b =ᶠ[𝓝 y]
      fun x => nativePhysicalFirstCorrectionFamily d r0 b (normalFrameRelativeActualParameter d r0 x) := by
  filter_upwards [hY.mem_nhds hy] with x hx
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hr := (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have hrx := (hd.2.2.2.2.1.2 x hx).1.ne'
  rw [physicalFirstCorrectionCoarseFamily_normal_form d x b hFrame hr hrx]
  unfold nativePhysicalFirstCorrectionFamily
  rw [hd.1.normalizedFirstCorrectionCovector_actual_parameter hΩ hK r0 (hSub hx),
    hd.1.relativeCoframeNormalSobolev_actual_parameter (hSub hx) 1 r0 b,
    nativePhysicalFirstCorrectionScalar_actual_parameter d r0 hr0 x b hr hrx]

end ShrinkingSpheres
