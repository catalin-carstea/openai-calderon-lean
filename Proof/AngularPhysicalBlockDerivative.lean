import Proof.RelativeAngularDerivativeCurve
import Proof.PhysicalHarmonicBlockCasimir
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Differentiation along the actual normalized angular curve preserves
an exact scalar relation between SAME physical harmonic blocks. -/
lemma angular_half_block_of_coarse_relation
    (g : MetricField)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (V : Set NormalFrameRelativeParameter) (hV : IsOpen V)
    (p : NormalFrameRelativeParameter) (hp : normalFrameRelativeNormalization g p ∈ V)
    (hF : DifferentiableAt ℝ F (normalFrameRelativeNormalization g p))
    (hS : DifferentiableAt ℝ S (normalFrameRelativeNormalization g p))
    (c : ℕ → ℕ → ℝ)
    (hBlocks : ∀ q ∈ V,∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S q (sphereSobolevSingleL (1/2:ℝ) n z))=
        c m n • coarsePhysicalHarmonicBlock (F q) m n z)
    (i j : I) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (normalFrameRelativeAngularDerivative g S i j p (sphereSobolevSingleL (1/2:ℝ) n z))=
      c m n • coarsePhysicalHarmonicBlock (normalFrameRelativeAngularDerivative g F i j p) m n z := by
  let curve := normalFrameRelativeAngularCurve g p i j
  have hc := hasDerivAt_normalFrameRelativeAngularCurve g p i j
  have h0V : curve 0 ∈ V := by
    simpa only [curve,normalFrameRelativeAngularCurve_zero] using hp
  have hcV : ∀ᶠ θ : ℝ in 𝓝 0,curve θ ∈ V := hc.continuousAt.eventually (hV.mem_nhds h0V)
  have hSD := hasDerivAt_relativeAngularFamily g S p i j hS
  have hFD := hasDerivAt_relativeAngularFamily g F p i j hF
  have hs := (sphereSobolevCoefficientL (-(1/2:ℝ)) m).hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hSD.clm_apply (hasDerivAt_const (0:ℝ) (sphereSobolevSingleL (1/2:ℝ) n z)))
  have hf := ((sphereSobolevCoefficientL 0 m).hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hFD.clm_apply (hasDerivAt_const (0:ℝ) (sphereSobolevSingleL 1 n z)))).const_smul (c m n)
  have hEq : (fun θ : ℝ => sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (S (curve θ) (sphereSobolevSingleL (1/2:ℝ) n z))) =ᶠ[𝓝 0]
      (fun θ => c m n • sphereSobolevCoefficientL 0 m (F (curve θ) (sphereSobolevSingleL 1 n z))) :=
    hcV.mono (fun θ hθ => hBlocks (curve θ) hθ m n z)
  have hh := hs.unique (hf.congr_of_eventuallyEq hEq)
  simpa only [Function.comp_def,zero_apply,map_zero,zero_add,add_zero,coarsePhysicalHarmonicBlock,
    ContinuousLinearMap.comp_apply] using hh
end ShrinkingSpheres
