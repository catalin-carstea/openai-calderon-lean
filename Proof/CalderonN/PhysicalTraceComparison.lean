module

public import Proof.CalderonN.PhysicalTraceModelAdjoint
public import Proof.CalderonN.MovingTraceTwoComponentComparison

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Assemble the physical output, the signed harmonic model and its
exact adjoint in the quadratic comparison used for coercivity. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem physicalTrace_comparison_of_error_estimates (hn : 3 ≤ dim)
    {Y : Set (X dim)} (hY : IsOpen Y) {K : ℝ} (hK : 0 < K)
    {d : Data dim} (hγ : Elliptic Y K d.γ)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    (E : HarmonicTestExpansion Y d.γ d.frame v) (D : AngularModelData E d.radius)
    (P U Ud J : Module.End ℝ (SmoothSupportedTraceSection Y)) (Cerr Cj : ℝ) :
    let T := physicalRaisingModel hY hγ hK he hlog hA hEll S
    let L := physicalLoweringModel hY hγ hK he hlog hA hEll S
    let Td := L-physicalTraceModelCorrection hY he hA hEll S hlog
    let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hγ.contDiffOn_density hK)
    let u := E.traceComponent Complex.reCLM
    let w := E.traceComponent Complex.imCLM
    P = (2:ℝ) • T+U+J →
    traceNorm Y d v = Real.sqrt (B (P u) (P u)+B (P w) (P w)) →
    PairedAdjoint B U Ud →
    |movingTraceAdjointErrorForm B T Td L U Ud u+movingTraceAdjointErrorForm B T Td L U Ud w| ≤ Cerr →
    Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ Cj →
    ∃ a : ℝ, 0 ≤ a ∧ 4*(D.raisingSquare-D.loweringSquare) ≤ a^2+Cerr ∧
      a ≤ traceNorm Y d v+Cj := by
  dsimp only
  intro hP hOutput hAdj hErr hJ
  let T := physicalRaisingModel hY hγ hK he hlog hA hEll S
  let L := physicalLoweringModel hY hγ hK he hlog hA hEll S
  let Td := L-physicalTraceModelCorrection hY he hA hEll S hlog
  let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hγ.contDiffOn_density hK)
  let u := E.traceComponent Complex.reCLM
  let w := E.traceComponent Complex.imCLM
  have hSym (a b : SmoothSupportedTraceSection Y) : B a b = B b a :=
    smoothSupportedTracePairing_symm hn _ _ _
  have hPos (a : SmoothSupportedTraceSection Y) : 0 ≤ B a a :=
    smoothSupportedTracePairing_self_nonneg hn _ (fun _ => Real.sqrt_nonneg _) _
  have hT : PairedAdjoint B T Td := pairedAdjoint_physicalRaisingModel hY hγ hK he hframe hn hA hEll S hlog
  obtain ⟨a,ha,hGap,hNorm⟩ := movingTrace_twoComponent_comparison B hSym hPos
    P T Td L U Ud J hP u w hT hAdj Cerr Cj hErr hJ
  have hR : D.raisingSquare = B (T u) (T u)+B (T w) (T w) :=
    physicalRaisingModel_pairing hY hγ hK he hlog hA hEll S hframe hv D
  have hL : D.loweringSquare = B (L u) (L u)+B (L w) (L w) :=
    physicalLoweringModel_pairing hY hγ hK he hlog hA hEll S hframe hv D
  rw [hR,hL]
  exact ⟨a,ha,hGap,hOutput.symm ▸ hNorm⟩

end CalderonN
