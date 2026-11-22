module

public import Proof.Manuscript.MovingTrace.VelocityChartPlaneRegularity
public import Proof.Manuscript.MovingTrace.VelocityChartAdjointPairings
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

/-- A local response to compactly supported plane waves reconstructs the
literal angular adjoint acting on every localized smooth sphere datum. -/
theorem velocity_chart_quantization
    (A : SmoothRadialVelocity G) {p : P} (hp : p ∈ A.U)
    {χ η : Z → ℂ} (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hηS : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E} (hKζ : IsCompact Kζ)
    (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) (hOne : EqOn ζ 1 (angularChartSupport C.pole η))
    {s : Q → E → ℂ} (hS : Continuous fun q : E × E => s (p,q.1) q.2)
    {B : ℝ} (hB : 0 ≤ B) (hGrowth : ∀ x ξ, ‖s (p,x) ξ‖ ≤ B*(1+‖ξ‖))
    (hExact : ∀ x ξ, s (p,x) ξ = C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ)
    (u : Z → ℂ) (hu : smoothNear u S) (x : E) :
    let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
    let integrand := fun ξ => angularFourierPhase (dim := n+1) x ξ * s (p,x) ξ * angularFourierTransform (dim := n+1) f ξ
    Integrable f ∧ Integrable integrand ∧
      χ (angularPoint C.pole x) * A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
        ∫ ξ, integrand ξ := by
  let κ := stereographic' ((n+1)-1) C.pole
  let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
  let φ := fun z => η z * u z
  let K (q : ↥S × E) := χ q.1 * A.operator p (C.chartPlaneWave ζ p q.2) q.1
  let H (w : ↥S) := χ w * A.operator p φ w
  let ζ' (w : ↥S) := C.chartPlaneWave ζ p 0 w
  have hζS := C.chartPlaneWave_contDiff hζ hKζ hζ₀
  obtain ⟨hfs,hfc⟩ := compactSmooth_angularDatum C.pole hη hu hηS
  obtain ⟨U₀,hU₀,hSU₀,hχU₀⟩ := hχ
  obtain ⟨U₁,hU₁,hSU₁,hηU₁⟩ := hη
  obtain ⟨U₂,hU₂,hSU₂,huU₂⟩ := hu
  have hχC : Continuous (fun w : ↥S => χ w) :=
    hχU₀.continuousOn.comp_continuous continuous_subtype_val (fun w => hSU₀ w.property)
  have hφ : smoothNear φ S := ⟨U₁∩U₂,hU₁.inter hU₂,subset_inter hSU₁ hSU₂,
    (hηU₁.mono inter_subset_left).mul (huU₂.mono inter_subset_right)⟩
  have hHC : Continuous H := hχC.mul (A.operator_continuous_on_sphere hp hφ)
  have hζ'C : Continuous ζ' :=
    hζS.continuous.comp ((continuous_const (y := (p,(0:E)))).prodMk continuous_subtype_val)
  have hSrc : κ.source = {C.pole}ᶜ := by simp only [κ,stereographic'_source]
  have hRead : Measurable κ := measurable_of_continuousOn_compl_singleton C.pole (hSrc ▸ κ.continuousOn)
  obtain ⟨hKC,hKB,hKChart⟩ := C.velocity_chart_planeResponse_regular A p hχS ζ hS hB hGrowth hExact
  let w : ↥S := κ.symm x
  have hxT : x ∈ κ.target := by simp [κ]
  have hw : w ∈ κ.source := κ.map_target hxT
  have hwX : κ w = x := κ.right_inv hxT
  have hKX (ξ : E) : K (w,ξ) = angularFourierPhase (dim := n+1) x ξ * s (p,x) ξ := by
    calc
      _ = angularFourierPhase (dim := n+1) (κ w) ξ * s (p,κ w) ξ := hKChart w hw ξ
      _ = _ := by rw [hwX]
  have hPair := C.velocity_chart_adjoint_pairings A (p := p) (χ := χ) (η := η) (ζ := ζ) hp
    ⟨U₀,hU₀,hSU₀,hχU₀⟩ ⟨U₁,hU₁,hSU₁,hηU₁⟩ hηS hζ hKζ hζ₀ hOne u ⟨U₂,hU₂,hSU₂,huU₂⟩
  have hExactInt : H w = ∫ ξ, K (w,ξ) * angularFourierTransform (dim := n+1) f ξ :=
    angularFourier_reconstruct_from_sphere_pairings (dim := n+1) (f := f) (K := K)
      (G := H) (ζ := ζ') (read := κ) hfs hfc hKC hB hKB hHC hζ'C hRead hPair w
  have hFourier := angularFourierTransform_continuous (d := n+1) f hfs hfc
  have h0 : Integrable (fun ξ => ‖angularFourierTransform (dim := n+1) f ξ‖) := by
    simpa only [pow_zero,one_mul] using angularFourierTransform_integrable_norm_weight (d := n+1) f hfs hfc 0
  have h1 := angularFourierTransform_integrable_norm_weight (d := n+1) f hfs hfc 1
  have hBInt : Integrable (fun ξ => B*(‖angularFourierTransform (dim := n+1) f ξ‖ +
      ‖ξ‖ ^ (1:ℕ) * ‖angularFourierTransform (dim := n+1) f ξ‖)) := (h0.add h1).const_mul B
  have hIntegrable : Integrable (fun ξ => K (w,ξ) * angularFourierTransform (dim := n+1) f ξ) :=
    hBInt.mono' (((hKC.comp ((continuous_const (y := w)).prodMk continuous_id)).mul hFourier).aestronglyMeasurable)
      (.of_forall fun ξ => by
        rw [norm_mul,pow_one]
        refine (mul_le_mul_of_nonneg_right (hKB w ξ) (norm_nonneg _)).trans_eq ?_
        ring)
  simp only [hKX] at hExactInt hIntegrable
  exact ⟨(angularFourier_inversion (d := n+1) f hfs hfc x).1,hIntegrable,hExactInt⟩

end SignedPoissonCollar
end CalderonPaper
