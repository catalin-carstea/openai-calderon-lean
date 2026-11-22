module

public import Proof.Manuscript.MovingTrace.VelocityChartDatumRestriction
public import Proof.Manuscript.AngularFourierResponse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

/-- The Fourier reconstruction test pairs the actual angular adjoint
with an arbitrary real smooth ambient test function. -/
theorem velocity_chart_adjoint_pairings
    (A : SmoothRadialVelocity G) {p : P} (hp : p ∈ A.U)
    {χ η : Z → ℂ} (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hηS : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E} (hKζ : IsCompact Kζ)
    (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) (hOne : EqOn ζ 1 (angularChartSupport C.pole η))
    (u : Z → ℂ) (hu : smoothNear u S) :
    let κ := stereographic' ((n+1)-1) C.pole
    let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
    let φ := fun z => η z * u z
    let K (q : ↥S × E) := χ q.1 * A.operator p (C.chartPlaneWave ζ p q.2) q.1
    let H (w : ↥S) := χ w * A.operator p φ w
    let ζ' (w : ↥S) := C.chartPlaneWave ζ p 0 w
    ∀ (t : Z → ℝ), ContDiff ℝ ∞ t →
      ∃ v : ↥S → ℂ, Continuous v ∧
        (∀ ξ, (∫ w : ↥S, K (w,ξ)*(t w : ℂ) ∂sphereProbability (n+1)) =
          ∫ w : ↥S, ζ' w*angularFourierPhase (dim := n+1) (κ w) ξ*v w ∂sphereProbability (n+1)) ∧
        (∫ w : ↥S, H w*(t w : ℂ) ∂sphereProbability (n+1)) =
          ∫ w : ↥S, ζ' w*f (κ w)*v w ∂sphereProbability (n+1) := by
  dsimp only
  intro t ht
  let κ := stereographic' ((n+1)-1) C.pole
  let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
  let φ := fun z => η z * u z
  let K (q : ↥S × E) := χ q.1 * A.operator p (C.chartPlaneWave ζ p q.2) q.1
  let H (w : ↥S) := χ w * A.operator p φ w
  let ζ' (w : ↥S) := C.chartPlaneWave ζ p 0 w
  have hζS := C.chartPlaneWave_contDiff hζ hKζ hζ₀
  obtain ⟨U₀,hU₀,hSU₀,hχU₀⟩ := hχ
  obtain ⟨U₁,hU₁,hSU₁,hηU₁⟩ := hη
  obtain ⟨U₂,hU₂,hSU₂,huU₂⟩ := hu
  have hφ : smoothNear φ S := ⟨U₁∩U₂,hU₁.inter hU₂,subset_inter hSU₁ hSU₂,
    (hηU₁.mono inter_subset_left).mul (huU₂.mono inter_subset_right)⟩
  let g (z : Z) := χ z * (t z : ℂ)
  let v (w : ↥S) := fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z)) g) w
    (A.velocity (p,w))
  have hg : smoothNear g S := ⟨U₀,hU₀,hSU₀,
    hχU₀.mul (Complex.ofRealCLM.contDiff.comp ht).contDiffOn⟩
  have hP := A.complexFixedBallPoisson_contDiff hp hg
  have hV : Continuous (fun w : ↥S => A.velocity (p,w)) := A.smoothV.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_subtype_val) (fun w => ⟨hp,A.sphere_mem w.property⟩)
  have hv : Continuous v := ((hP.fderiv_right (m := ∞) (by simp)).continuous.comp
    continuous_subtype_val).clm_apply hV
  refine ⟨v,hv,?_,?_⟩
  · intro ξ
    have hPlaneC : ContDiff ℝ ∞ (C.chartPlaneWave ζ p ξ) :=
      hζS.comp ((contDiff_const (c := (p,ξ))).prodMk contDiff_id)
    have hPlane : smoothNear (C.chartPlaneWave ζ p ξ) S :=
      ⟨univ,isOpen_univ,subset_univ _,hPlaneC.contDiffOn⟩
    calc
      _ = ∫ w : ↥S, A.operator p (C.chartPlaneWave ζ p ξ) w * g w ∂sphereProbability (n+1) := by
        apply integral_congr_ae
        filter_upwards with w
        change χ w * A.operator p (C.chartPlaneWave ζ p ξ) w * (t w : ℂ) = _
        simp only [g]
        ring
      _ = ∫ w : ↥S, C.chartPlaneWave ζ p ξ w * v w ∂sphereProbability (n+1) :=
        A.integral_operator_pairing (p := p) (φ := C.chartPlaneWave ζ p ξ) (g := g) hp hPlane hg
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with w
        rw [C.chartPlaneWave_restrict_sphere]
  · calc
      _ = ∫ w : ↥S, A.operator p φ w * g w ∂sphereProbability (n+1) := by
        apply integral_congr_ae
        filter_upwards with w
        simp only [H,g]
        ring
      _ = ∫ w : ↥S, φ w * v w ∂sphereProbability (n+1) :=
        A.integral_operator_pairing (p := p) (φ := φ) (g := g) hp hφ hg
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with w
        rw [show φ w = ζ' w*f (κ w) from C.localizedDatum_eq_chartPlaneWaveZero ζ p η u hηS hOne w]

end SignedPoissonCollar
end CalderonPaper
