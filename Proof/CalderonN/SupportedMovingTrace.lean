module

public import Proof.CalderonN.PhysicalTraceIdentification
public import Proof.CalderonN.MovingTraceDuality

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! The protected moving trace acts on real smooth compactly supported
sections whenever its physical fiber adjoints have been identified. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {γ g₁ g₂ : MetricField dim} {e : Frame dim}
variable (hY : IsOpen Y) {K : ℝ} (hγ : Elliptic Y K γ) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair γ x (e x i) (e x j) = if i=j then 1 else 0)
variable {E : X dim × X dim → X dim} {r : X dim → ℝ} {A : TraceAdjoint dim}
  (hA : IsMovingTraceAdjoint Y γ g₁ e E r A)

@[expose] def MovingAdjointFiberMatches
    (γ : MetricField dim) (e : Frame dim) (A : TraceAdjoint dim) (i : I dim)
    (C : X dim → Module.End ℝ (SmoothSphereTrace dim)) (L : ℂ →L[ℝ] ℝ) : Prop :=
  ∀ (v : Field dim), smoothNear v (bundle Y γ) → ∀ (u : SmoothSupportedTraceSection Y),
    TraceComponentMatches e L v u →
    ∀ x ∈ Y,∀ z : UnitSphere dim,
      (C x (smoothSupportedTraceFiberL x u)).1 z = L (adjointField A i v (x,frameVector e x z))

include hY hγ he hframe hA in
theorem smoothSupportedTraceFiberRegular_movingAdjoint
    (i : I dim) (C : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hC : MovingAdjointFiberMatches (Y:=Y) γ e A i C Complex.reCLM) :
    SmoothSupportedTraceFiberRegular Y C := by
  intro u
  obtain ⟨v,hv,hRep⟩ := exists_physical_real_trace_representative hY hγ he hframe u
  obtain ⟨U,hU,hBU,hF⟩ := (hA i v hv).1
  let P := X dim × X dim
  let W₀ : Set P := Prod.fst ⁻¹' Y
  let W : Set P := W₀ ∩ movingBallFromFrame e ⁻¹' U
  have hW₀ : IsOpen W₀ := hY.preimage continuous_fst
  have hMf : ContDiffOn ℝ ∞ (movingBallFromFrame e) W₀ := contDiffOn_movingBallFromFrame_local he
  have hW : IsOpen W := hMf.continuousOn.isOpen_inter_preimage hW₀ hU
  refine ⟨W,fun p => (adjointField A i v (movingBallFromFrame e p)).re,
    hW,?_,Complex.reCLM.contDiff.comp_contDiffOn (hF.comp (hMf.mono inter_subset_left) (fun _ hq => hq.2)),?_⟩
  · intro p hp
    exact ⟨hp.1,hBU (movingBallFromFrame_sphere hframe hp)⟩
  · intro x hx z
    exact (hC v hv u hRep x hx z).symm

variable (C : I dim → X dim → Module.End ℝ (SmoothSphereTrace dim))
  (hC : ∀ i, SmoothSupportedTraceFiberRegular Y (C i))

@[expose] def supportedTraceDerivative (i : I dim) : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  supportedHorizontal hY hγ hK he (fun _ => axis i) contDiffOn_const+
    smoothSupportedTraceFiberAction hY (C i) (hC i)

include hframe in
theorem supportedTraceDerivative_matches
    (L : ℂ →L[ℝ] ℝ) (hMatch : ∀ i,MovingAdjointFiberMatches (Y:=Y) γ e A i (C i) L)
    {v : Field dim} (hv : smoothNear v (bundle Y γ)) {u : SmoothSupportedTraceSection Y}
    (hu : TraceComponentMatches e L v u) (i : I dim) :
    TraceComponentMatches e L (traceDerivative γ A i v) (supportedTraceDerivative hY hγ hK he C hC i u) := by
  intro x hx z
  have hH := supportedHorizontal_matches_physical hY hγ hK he hframe (fun _ => axis i)
    contDiffOn_const hv L u hu x hx z
  have hAA : (smoothSupportedTraceFiberAction hY (C i) (hC i) u).1 (x,z) =
      L (adjointField A i v (x,frameVector e x z)) := by
    rw [← smoothSupportedTraceFiberL_apply x,smoothSupportedTraceFiberAction_fiber]
    exact hMatch i v hv u hu x hx z
  simp only [supportedTraceDerivative,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,
    hH,hAA,traceDerivative,map_add]

variable (hr : ContDiffOn ℝ ∞ r Y)
  (hQ : ∀ i j, ContDiffOn ℝ ∞ (fun y => principal γ g₂ y i j) Y)
  (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => drift γ g₂ y i) Y)

@[expose] def supportedMovingTrace :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  let W := supportedTraceDerivative hY hγ hK he C hC
  smoothSupportedTraceBaseMul hY r hr *
    ((∑ i : I dim,∑ j : I dim, smoothSupportedTraceBaseMul hY (fun y => principal γ g₂ y i j) (hQ i j) *
      (W i*W j-∑ k : I dim, smoothSupportedTraceBaseMul hY (fun y => christoffel γ y k i j)
        (hγ.contDiffOn_christoffel hY hK k i j)*W k))+
    ∑ k : I dim, smoothSupportedTraceBaseMul hY (fun y => drift γ g₂ y k) (hb k)*W k)

include hframe hA in
theorem supportedMovingTrace_matches
    (L : ℂ →L[ℝ] ℝ) (hMatch : ∀ i,MovingAdjointFiberMatches (Y:=Y) γ e A i (C i) L)
    {v : Field dim} (hv : smoothNear v (bundle Y γ)) {u : SmoothSupportedTraceSection Y}
    (hu : TraceComponentMatches e L v u) :
    TraceComponentMatches e L (movingTrace γ g₂ r A v) (supportedMovingTrace hY hγ hK he C hC hr hQ hb u) := by
  let D := supportedTraceDerivative hY hγ hK he C hC
  have h₁ (i : I dim) : TraceComponentMatches e L (traceDerivative γ A i v) (D i u) :=
    supportedTraceDerivative_matches hY hγ hK he hframe C hC L hMatch hv hu i
  have h₂ (i j : I dim) :
      TraceComponentMatches e L (traceDerivative γ A i (traceDerivative γ A j v)) (D i (D j u)) :=
    supportedTraceDerivative_matches hY hγ hK he hframe C hC L hMatch
      (smoothNear_traceDerivative hY (hγ.smoothMetric hK) hA hv j) (h₁ j) i
  intro x hx z
  have hh₁ (i : I dim) := h₁ i x hx z
  have hh₂ (i j : I dim) := h₂ i j x hx z
  have hL (a : ℝ) (b : ℂ) : L ((a:ℂ)*b) = a*L b := map_smul L a b
  change ((smoothSupportedTraceBaseMul hY r hr *
      ((∑ i : I dim,∑ j : I dim,smoothSupportedTraceBaseMul hY (fun y => principal γ g₂ y i j) (hQ i j) *
        (D i*D j-∑ k : I dim,smoothSupportedTraceBaseMul hY (fun y => christoffel γ y k i j)
          (hγ.contDiffOn_christoffel hY hK k i j)*D k))+
        ∑ k : I dim,smoothSupportedTraceBaseMul hY (fun y => drift γ g₂ y k) (hb k)*D k)) u).1 (x,z) = _
  simp only [movingTrace,Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.sum_apply,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_sum,Pi.add_apply,Pi.sub_apply,Finset.sum_apply,
    supportedTraceBaseMul_apply,hh₁,hh₂,hL,map_add,map_sub,map_sum]
  simp only [mul_add,mul_sub,Finset.mul_sum]

end CalderonN
