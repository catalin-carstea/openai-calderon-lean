module

public import Proof.CalderonN.ActualSupportedGaussFiber

import Proof.CalderonN.MetricSmooth
import Proof.CalderonN.PrincipalMetric
import Mathlib.Tactic

/-! The norm measured by the frozen Proposition 5.3 caller is the
pairing norm of the actual common-domain moving trace operator. -/

public section

noncomputable section
open Set
open scoped ContDiff Classical
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem contDiffOn_drift_entry {Y : Set (X dim)} (hY : IsOpen Y)
    {γ g₂ : MetricField dim} (hγ : SmoothMetric Y γ) (hg₂ : SmoothMetric Y g₂) (k : I dim) :
    ContDiffOn ℝ ∞ (fun x => drift γ g₂ x k) Y :=
  ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (contDiffOn_principal_entry hγ hg₂ i j).mul
    ((contDiffOn_christoffel hY hγ k i j).sub (contDiffOn_christoffel hY hg₂ k i j))

theorem supportedMovingTrace_traceNorm (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y)
    {d : Data dim} {K : ℝ} (hγ : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    (hAdj : IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint)
    (C : I dim → X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (C i)) (hr : ContDiffOn ℝ ∞ d.radius Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    (hRe : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (C i) Complex.reCLM)
    (hIm : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (C i) Complex.imCLM)
    {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) (D : HarmonicTestExpansion Y d.γ d.frame v) :
    let P := supportedMovingTrace hY hγ hK he C hC hr hQ hb
    let u := P (D.traceComponent Complex.reCLM)
    let w := P (D.traceComponent Complex.imCLM)
    traceNorm Y d v = Real.sqrt (smoothSupportedTracePairing hn (chartVolume d.γ) u u+
      smoothSupportedTracePairing hn (chartVolume d.γ) w w) := by
  let P := supportedMovingTrace hY hγ hK he C hC hr hQ hb
  exact congrArg Real.sqrt (outputSq_eq_supportedTracePairings (e:=d.frame) hn hY (hγ.contDiffOn_density hK)
    (movingTrace d.γ d.g₂ d.radius d.adjoint v) (P (D.traceComponent Complex.reCLM))
      (P (D.traceComponent Complex.imCLM))
    (supportedMovingTrace_matches hY hγ hK he hframe hAdj C hC hr hQ hb Complex.reCLM hRe hv
      (fun _ hx z => D.traceComponent_apply Complex.reCLM hx z))
    (supportedMovingTrace_matches hY hγ hK he hframe hAdj C hC hr hQ hb Complex.imCLM hIm hv
      (fun _ hx z => D.traceComponent_apply Complex.imCLM hx z)))

theorem actualSupportedMovingTrace_exists (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hrρ : ∀ y ∈ Y, 2*d.radius y < ρ)
    (F : ∀ y ∈ Y,ActualGaussFiberData d y) :
    ∃ P : Module.End ℝ (SmoothSupportedTraceSection Y),
      (∀ {v : Field dim}, smoothNear v (bundle Y d.γ) → ∀ u : SmoothSupportedTraceSection Y,
        TraceComponentMatches d.frame Complex.reCLM v u →
        TraceComponentMatches d.frame Complex.reCLM (movingTrace d.γ d.g₂ d.radius d.adjoint v) (P u)) ∧
      (∀ {v : Field dim}, smoothNear v (bundle Y d.γ) → ∀ u : SmoothSupportedTraceSection Y,
        TraceComponentMatches d.frame Complex.imCLM v u →
        TraceComponentMatches d.frame Complex.imCLM (movingTrace d.γ d.g₂ d.radius d.adjoint v) (P u)) ∧
      ∀ {v : Field dim}, smoothNear v (bundle Y d.γ) → ∀ D : HarmonicTestExpansion Y d.γ d.frame v,
        let u := P (D.traceComponent Complex.reCLM)
        let w := P (D.traceComponent Complex.imCLM)
        traceNorm Y d v = Real.sqrt (smoothSupportedTracePairing hn (chartVolume d.γ) u u+
          smoothSupportedTracePairing hn (chartVolume d.γ) w w) := by
  let C (i : I dim) (y : X dim) := if hy : y ∈ Y then (F y hy).adjoint i else 0
  have hMatches (i : I dim) :
      MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (C i) Complex.reCLM ∧
        MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (C i) Complex.imCLM :=
    actualGaussFiber_matches (by omega : 2 ≤ dim) hY hΩ hd hK hrρ F i
  have hYΩ : Y ⊆ Ω := fun _ hy => hd.2.1.center_mem hy
  have hγ : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hYΩ,fun x hx => hd.1.1.2 x (hYΩ hx)⟩
  have h₂ : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hYΩ,fun x hx => hd.1.2.2.1.2 x (hYΩ hx)⟩
  have he (i : I dim) := (hd.1.2.2.2.2.2.2.1 i).mono hYΩ
  have hframe (x : X dim) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hYΩ hx)
  have hAdj := hd.2.2.2.1
  have hReg (i : I dim) : SmoothSupportedTraceFiberRegular Y (C i) :=
    smoothSupportedTraceFiberRegular_movingAdjoint hY hγ he hframe hAdj i (C i) (hMatches i).1
  have hQ (i j : I dim) := contDiffOn_principal_entry (hγ.smoothMetric hK) (h₂.smoothMetric hK) i j
  have hb (i : I dim) := contDiffOn_drift_entry hY (hγ.smoothMetric hK) (h₂.smoothMetric hK) i
  let P := supportedMovingTrace hY hγ hK he C hReg hd.2.2.2.2.1.1 hQ hb
  have hRe {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) (u : SmoothSupportedTraceSection Y)
      (hu : TraceComponentMatches d.frame Complex.reCLM v u) :
      TraceComponentMatches d.frame Complex.reCLM (movingTrace d.γ d.g₂ d.radius d.adjoint v) (P u) :=
    supportedMovingTrace_matches hY hγ hK he hframe hAdj C hReg hd.2.2.2.2.1.1 hQ hb
      Complex.reCLM (fun i => (hMatches i).1) hv hu
  have hIm {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) (u : SmoothSupportedTraceSection Y)
      (hu : TraceComponentMatches d.frame Complex.imCLM v u) :
      TraceComponentMatches d.frame Complex.imCLM (movingTrace d.γ d.g₂ d.radius d.adjoint v) (P u) :=
    supportedMovingTrace_matches hY hγ hK he hframe hAdj C hReg hd.2.2.2.2.1.1 hQ hb
      Complex.imCLM (fun i => (hMatches i).2) hv hu
  refine ⟨P,hRe,hIm,?_⟩
  intro v hv D
  exact supportedMovingTrace_traceNorm hn hY hγ hK he hframe hAdj C hReg hd.2.2.2.2.1.1 hQ hb
    (fun i => (hMatches i).1) (fun i => (hMatches i).2) hv D

end CalderonN
