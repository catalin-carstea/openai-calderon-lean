module

public import Proof.CalderonN.ActualTraceSections
public import Proof.CalderonN.RemainderAbsorption
public import Proof.CalderonN.SmoothTraceAngularOrder

import Proof.CalderonN.ActualGaussConormalBounds
import Proof.CalderonN.SmoothSupportedTraceBaseCommutation
import Proof.CalderonN.SmoothBesselSections
import Proof.CalderonN.SmoothTraceSobolevCompletion
import Mathlib.Tactic

/-! An angular order-one estimate for a genuine fiber operator gives
the inverse-floor bound in the protected physical energy. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem norm_smoothSphereTraceSobolev_zero_eq (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn 0 (by norm_num) u‖ = ‖smoothSphereTraceL2 hn u‖ := by
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let v : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  change ‖smoothSphereTraceSobolev hn 0 (by norm_num) (smoothSphereTrace v)‖ =
    ‖smoothSphereTraceL2 hn (smoothSphereTrace v)‖
  rw [smoothSphereTraceSobolev_apply,smoothSphereTraceL2_apply,norm_smoothBoundarySobolev_zero_eq]

theorem norm_smoothTrace_orderOne_to_L2 (hn : 3 ≤ dim)
    (A A' : Module.End ℝ (SmoothSphereTrace dim)) (C : ℝ) (hC : 0 ≤ C)
    (hAdj : SmoothTraceAdjoint hn A A') (hC₁ : SmoothTraceAngularBound hn 1 C A)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceL2 hn (A u)‖ ≤ C*‖smoothSphereTraceSobolev hn 1 (by norm_num) u‖ := by
  rw [← norm_smoothSphereTraceSobolev_zero_eq]
  apply norm_smoothTraceOperator_le_of_finite hn 1 0 (by norm_num) (by norm_num) (by norm_num)
    A A' hAdj C hC _ u
  intro f
  have hHalf (g : HarmonicFiniteCoefficients dim) := hC₁ (1:Fin 4) (2:Fin 4) (by decide) (finiteHarmonicSmoothTraceL g)
  have hHigh (g : HarmonicFiniteCoefficients dim) := hC₁ (2:Fin 4) (3:Fin 4) (by decide) (finiteHarmonicSmoothTraceL g)
  simp only [traceOrderNorm_half_eq,traceOrderNorm_negHalf_eq,traceOrderNorm_threeHalf_eq,
    finiteHarmonicSmoothTraceL_sobolev] at hHalf hHigh
  simpa only [add_self_div_two] using norm_finite_smoothTrace_midpoint hn A C C hC hC hHalf hHigh f

theorem sobolevSq_eq_supportedTraceComponents
    (hn : 3 ≤ dim) {g : MetricField dim} {e : Frame dim} {x : X dim}
    (hframe : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (v : X dim → ℂ) (U V : SmoothSupportedTraceSection Y)
    (hRe : ∀ z : UnitSphere dim,U.1 (x,z) = (v (frameVector e x z)).re)
    (hIm : ∀ z : UnitSphere dim,V.1 (x,z) = (v (frameVector e x z)).im)
    (s : ℝ) (hs : s ≤ 2) :
    sobolevSq g e s x v =
      ‖smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x U)‖^2+
      ‖smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x V)‖^2 := by
  let B (u : SmoothSupportedTraceSection Y) :=
    sphereHarmonicDecomposition.symm (smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x u))
  have hProj (u : SmoothSupportedTraceSection Y) (k : ℕ) :
      harmonicProjection k (B u) = besselWeight s k • harmonicProjection k (smoothSupportedTraceL2 hn u x) := by
    rw [← sphereHarmonicDecomposition_apply,show sphereHarmonicDecomposition (B u) =
      smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x u) from
        LinearIsometryEquiv.apply_symm_apply _ _,smoothSphereTraceSobolev_coordinate]
    rfl
  have hR := (smoothSupportedTraceL2_ae hn U x).trans (Filter.Eventually.of_forall hRe)
  have hI := (smoothSupportedTraceL2_ae hn V x).trans (Filter.Eventually.of_forall hIm)
  have hS := sobolevSq_eq_bessel_components hn g e x hframe v
    (smoothSupportedTraceL2 hn U x) (smoothSupportedTraceL2 hn V x) (B U) (B V) hR hI s
    (hProj U) (hProj V)
  simpa only [B,LinearIsometryEquiv.norm_map] using hS

theorem HarmonicTestExpansion.sobolevSq_eq_traceComponents
    (hn : 3 ≤ dim) {g : MetricField dim} {e : Frame dim} {v : Field dim}
    (E : HarmonicTestExpansion Y g e v) {x : X dim} (hx : x ∈ Y)
    (hframe : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) :
    sobolevSq g e s x (fun z => v (x,z)) =
      ‖smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x (E.traceComponent Complex.reCLM))‖^2+
      ‖smoothSphereTraceSobolev hn s hs (smoothSupportedTraceFiberL x (E.traceComponent Complex.imCLM))‖^2 := by
  exact sobolevSq_eq_supportedTraceComponents hn hframe (fun z => v (x,z))
    (E.traceComponent Complex.reCLM) (E.traceComponent Complex.imCLM)
    (E.traceComponent_apply Complex.reCLM hx) (E.traceComponent_apply Complex.imCLM hx) s hs

theorem physicalTrace_lowerOrder_bound_of_fiber_angularBounds
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hFloor : 1 ≤ floor) {v : Field dim} (hv : Test Y d.γ d.frame v)
    (E : HarmonicTestExpansion Y d.γ d.frame v)
    (J : Module.End ℝ (SmoothSupportedTraceSection Y)) (C : ℝ) (hC : 0 ≤ C)
    (hFiber : ∀ x ∈ Y,∃ A A' : Module.End ℝ (SmoothSphereTrace dim),
      SmoothTraceAdjoint hn A A' ∧ SmoothTraceAngularBound hn 1 C A ∧
      ∀ u, smoothSupportedTraceFiberL x (J u) = A (smoothSupportedTraceFiberL x u)) :
    let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hK)
    let u := E.traceComponent Complex.reCLM
    let w := E.traceComponent Complex.imCLM
    Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ C/floor*energyNorm Y d v := by
  dsimp only
  let u := E.traceComponent Complex.reCLM
  let w := E.traceComponent Complex.imCLM
  let μ := metricDensity d.γ
  let B := smoothSupportedTracePairingL hn hY μ (hg.contDiffOn_density hK)
  let Z := B (J u) (J u)+B (J w) (J w)
  have hμ (x : X dim) : 0 ≤ μ x := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := add_nonneg (smoothSupportedTracePairing_self_nonneg hn μ hμ _) 
    (smoothSupportedTracePairing_self_nonneg hn μ hμ _)
  change Real.sqrt Z ≤ C/floor*energyNorm Y d v
  refine remainder_norm_le_of_sobolev_one hn hY hg hK he hframe hp hFloor hv
    (Real.sqrt_nonneg _) hC ?_
  rw [Real.sq_sqrt hZ]
  have hIn₁ := (integrable_smoothSupportedTracePairing_integrand_local hn hY μ
    (hg.contDiffOn_density hK) (J u) (J u)).integrableOn (s:=Y)
  have hIn₂ := (integrable_smoothSupportedTracePairing_integrand_local hn hY μ
    (hg.contDiffOn_density hK) (J w) (J w)).integrableOn (s:=Y)
  simp only [real_inner_self_eq_norm_sq] at hIn₁ hIn₂
  change smoothSupportedTracePairing hn μ (J u) (J u)+smoothSupportedTracePairing hn μ (J w) (J w) ≤ _
  rw [smoothSupportedTracePairing_self_eq_setIntegral,smoothSupportedTracePairing_self_eq_setIntegral,
    ← integral_add hIn₁ hIn₂,← integral_const_mul]
  have hInt := hv.integrableOn_weighted_sobolev hn hY d.frame he hframe 1 (by norm_num) μ
    (hg.contDiffOn_density hK).continuousOn
  apply integral_mono_ae (hIn₁.add hIn₂) (hInt.const_mul _)
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  obtain ⟨A,A',hAdj,hAng,hEq⟩ := hFiber x hx
  have hPt (a : SmoothSupportedTraceSection Y) :
      ‖smoothSupportedTraceL2 hn (J a) x‖^2 ≤
        C^2*‖smoothSphereTraceSobolev hn 1 (by norm_num) (smoothSupportedTraceFiberL x a)‖^2 := by
    rw [← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    rw [smoothSupportedTraceL2,hEq a]
    exact norm_smoothTrace_orderOne_to_L2 hn A A' C hC hAdj hAng _
  let a := ‖smoothSupportedTraceL2 hn (J u) x‖
  let b := ‖smoothSupportedTraceL2 hn (J w) x‖
  let a₀ := ‖smoothSphereTraceSobolev hn 1 (by norm_num) (smoothSupportedTraceFiberL x u)‖
  let b₀ := ‖smoothSphereTraceSobolev hn 1 (by norm_num) (smoothSupportedTraceFiberL x w)‖
  have hS : sobolevSq d.γ d.frame 1 x (fun z => v (x,z)) = a₀^2+b₀^2 :=
    E.sobolevSq_eq_traceComponents hn hx (hframe x hx) 1 (by norm_num)
  change μ x*a^2+μ x*b^2 ≤ C^2*(μ x*sobolevSq d.γ d.frame 1 x (fun z => v (x,z)))
  rw [hS]
  calc
    μ x*a^2+μ x*b^2 ≤ μ x*(C^2*a₀^2)+μ x*(C^2*b₀^2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hPt u) (hμ x))
        (mul_le_mul_of_nonneg_left (hPt w) (hμ x))
    _ = C^2*(μ x*(a₀^2+b₀^2)) := by ring

end CalderonN
