module

public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.SmoothSupportedTraceAdjoints

import Proof.CalderonN.SmoothBesselSections
import Mathlib.Tactic

/-! The actual complex sections and their output norms in the common
real compactly supported domain. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim} {φ : Field dim}

@[expose] def smoothSupportedTraceOfAmbient (G : X dim × X dim → ℝ) (hG : ContDiff ℝ ∞ G)
    {K : Set (X dim)} (hK : IsCompact K) (hKY : K ⊆ Y)
    (hZero : ∀ x ∉ K, ∀ z : UnitSphere dim, G (x,z) = 0) :
    SmoothSupportedTraceSection Y :=
  ⟨fun p => G (p.1,p.2), ⟨G,hG,fun _ _ => rfl⟩,K,hK,hKY,hZero⟩

@[expose] def HarmonicTestExpansion.traceComponent (E : HarmonicTestExpansion Y g e φ)
    (L : ℂ →L[ℝ] ℝ) : SmoothSupportedTraceSection Y :=
  smoothSupportedTraceOfAmbient (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) E.compactSupportSet E.supportSubset
    (fun x hx z => by rw [E.representativeZero x hx z,map_zero])

theorem HarmonicTestExpansion.traceComponent_apply (E : HarmonicTestExpansion Y g e φ)
    (L : ℂ →L[ℝ] ℝ) {x : X dim} (hx : x ∈ Y) (z : UnitSphere dim) :
    (E.traceComponent L).1 (x,z) = L (φ (x,frameVector e x z)) :=
  congrArg L (E.representativeEq x hx z)

theorem HarmonicTestExpansion.traceComponent_L2 (E : HarmonicTestExpansion Y g e φ)
    (hn : 3 ≤ dim) (L : ℂ →L[ℝ] ℝ) (x : X dim) :
    smoothSupportedTraceL2 hn (E.traceComponent L) x =
      ambientSphereL2 (fun p => L (E.representative p)) (L.contDiff.comp E.representativeSmooth) x :=
  smoothSupportedTraceL2_eq_ambient hn _ _ (fun _ _ => rfl) x

theorem smoothSupportedTraceL2_ae (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y)
    (x : X dim) :
    (smoothSupportedTraceL2 hn u x : UnitSphere dim → ℝ) =ᵐ[unitSphereProbability dim]
      fun z => u.1 (x,z) := by
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  rw [smoothSupportedTraceL2_eq_ambient hn u hG hu]
  exact (ambientSphereL2_ae G hG x).trans (Filter.Eventually.of_forall fun z => (hu x z).symm)

theorem smoothSupportedTracePairing_self_eq_setIntegral (hn : 3 ≤ dim) (μ : X dim → ℝ)
    (u : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ u u = ∫ x in Y, μ x*‖smoothSupportedTraceL2 hn u x‖^2 := by
  unfold smoothSupportedTracePairing
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Y) (fun x hx => by
    rw [smoothSupportedTraceL2_eq_zero_off hn u hx,inner_zero_left,mul_zero])]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp only [real_inner_self_eq_norm_sq]

theorem outputSq_eq_supportedTracePairings (hn : 3 ≤ dim) (hY : IsOpen Y)
    (hμ : ContDiffOn ℝ ∞ (chartVolume g) Y) (F : Field dim)
    (u v : SmoothSupportedTraceSection Y)
    (hRe : ∀ x ∈ Y,∀ z : UnitSphere dim,u.1 (x,z) = (F (x,frameVector e x z)).re)
    (hIm : ∀ x ∈ Y,∀ z : UnitSphere dim,v.1 (x,z) = (F (x,frameVector e x z)).im) :
    outputSq Y g e F =
      smoothSupportedTracePairing hn (chartVolume g) u u +
        smoothSupportedTracePairing hn (chartVolume g) v v := by
  have hu := (integrable_smoothSupportedTracePairing_integrand_local hn hY _ hμ u u).integrableOn (s:=Y)
  have hv := (integrable_smoothSupportedTracePairing_integrand_local hn hY _ hμ v v).integrableOn (s:=Y)
  simp only [real_inner_self_eq_norm_sq] at hu hv
  rw [smoothSupportedTracePairing_self_eq_setIntegral,smoothSupportedTracePairing_self_eq_setIntegral,
    ← integral_add hu hv]
  apply setIntegral_congr_fun hY.measurableSet
  intro x hx
  have hFiber := fiberSq_eq_component_norms e x (fun z => F (x,z))
    (smoothSupportedTraceL2 hn u x) (smoothSupportedTraceL2 hn v x)
    ((smoothSupportedTraceL2_ae hn u x).trans (Filter.Eventually.of_forall (hRe x hx)))
    ((smoothSupportedTraceL2_ae hn v x).trans (Filter.Eventually.of_forall (hIm x hx)))
  change chartVolume g x*fiberSq e x _ = _
  rw [hFiber,mul_add]

end CalderonN
