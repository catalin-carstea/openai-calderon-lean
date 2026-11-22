module

public import Proof.CalderonN.CylinderGreenReproduction
public import Proof.CalderonN.CylinderTransferTaylor

import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.RadiusProfileGeometry
import Proof.CalderonN.TransferReproduction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Adapted from `ConformalGreenDensity` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Filter Metric Set MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

open FixedTube MovingSphere

@[expose] def complexDensity (ψ : (X dim) × (X dim) → ℝ) : (Field dim) := fun q => ψ q

/-- Boundary density representing the actual first-metric flux on each
sphere, for every smooth Dirichlet test on its closed normal ball. -/
@[expose] def IsGreenFluxDensity (Y : Set (X dim)) (d : (Data dim)) (G : (X dim) × (X dim) → ℝ) (ψ : (X dim) × (X dim) → ℝ) : Prop :=
  ∀ y ∈ Y, ∀ u, HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
    transferValue d (complexDensity ψ) u y = normalSphereGreenFlux d.g₁ d.expMap d.frame d.radius G y u

/-- The concrete analytical input still needed after continuation.
The density represents the flux of the same continued kernel and the
trace residual is controlled before selecting either small parameter. -/
@[expose] def UniformCylinderGreenFluxDensity (normal : I dim) (g₁ g₂ : (MetricField dim))
    (W Y' : Set (X dim)) (G₁ G₂ : (X dim) × (X dim) → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim)) (p : ℕ) (ρ R ε tb : ℝ) : Prop :=
  let Y := interior (coordinateCylinder normal)
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1,
    Small Y (conformalReference (depthScale normal 4) g₁ lam) (dilatedMetric g₂ lam)
      (shrinkingRadius R p (conformalDepth normal 4) δ) ε →
    ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ) (A : (TraceAdjoint dim)) (ψ : (X dim) × (X dim) → ℝ),
      let d := conformalSphereData normal g₁ g₂ E p R lam δ A
      IsOpen O ∧ ProductSolutionOn d.g₁ d.g₂ O G ∧
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        (endpoint d.expMap d.radius (y,frameVector d.frame y w),y) ∈ O) ∧
      EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' d.γ ρ d.expMap)) ∧
      Dirichlet Y d.γ d.g₁ d.expMap d.radius ∧
      IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius A ∧
      smoothNear ψ (bundle Y d.γ) ∧ IsGreenFluxDensity Y d G ψ ∧
      traceNorm Y d (cutoffDensity (cylinderCutoff normal 4 tb) (complexDensity ψ)) ≤ B

private theorem harmonicOnBall_of_normalCoordinates {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {ρ r u : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω γ E ρ) {y : (X dim)} (hy : y ∈ Y)
    (hr : 0 ≤ r y) (hrρ : r y ≤ ρ y) (hu : Harmonic Ω g u) :
    HarmonicOnBall g (closedBallImage γ E r y) u := by
  have hSub : closedBallImage γ E r y ⊆ Ω := by
    rintro _ ⟨v,hv,rfl⟩
    exact ((hN.2 y hy).2.2 v (hv.trans (pow_le_pow_left₀ hr hrρ 2))).1
  exact ⟨⟨Ω,hΩ,hSub,hu.1⟩,fun x hx => hu.2 x (hSub (interior_subset hx))⟩

set_option maxHeartbeats 1700000 in
/-- The exact flux representation supplies the constant, affine and paired
moments, while the endpoint Taylor bounds and volume floor are geometric. -/
theorem conformalCylinderTransfer_of_uniformGreenFluxDensity (hn : 3 ≤ dim)
    {Ω W Y' : Set (X dim)} (hΩ : IsOpen Ω) (hside : ContainsAlignedSide normal Ω W)
    (hY' : interior (coordinateCylinder normal) ⊆ Y')
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁)
    {n : ℕ} {u₁ u₂ : Fin n → (X dim) → ℝ} (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a))
    (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a)) (hpair : ∀ a, EqOn (u₁ a) (u₂ a) W)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {p : ℕ} {ρ R ε tb K c₀ floor : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hρ : 0 < ρ) (hK : 0 < K)
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hDensity : UniformCylinderGreenFluxDensity normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb) :
    ConformalCylinderTransfer normal g₁ g₂ E p R ε tb u₁ u₂ := by
  have h₀ : (0 : (X dim)) ∈ Ω := by
    obtain ⟨_,_,_,h0,hSub,_,_,_,_⟩ := hside
    exact hSub h0
  obtain ⟨ct,hct,hTaylor⟩ := exists_uniform_conformalCylinder_pair_remainder hΩ h₀ (fun a => (hu₁ a).1)
    hE hK hρ.le hSetup
  obtain ⟨cf,hcf,hFloor⟩ := exists_uniform_conformalCylinder_volumeFloor (normal := normal) hg₁
  obtain ⟨B,hB,hProduce⟩ := hDensity
  have hChart := eventually_cylinder_green_chart hΩ hside
  let Y := interior (coordinateCylinder normal)
  have hYO : Y ⊆ ball (0 : (X dim)) 3 := interior_subset.trans
    ((coordinateCylinder_subset_closedBall (normal := normal)).trans (closedBall_subset_ball (by norm_num)))
  refine ⟨ct,cf,B,hct,hcf,hB,?_⟩
  filter_upwards [hProduce,hChart,hSetup,hFloor,hTaylor] with lam hp hRooms hS hFloor hTaylor hpos δ hδ hSmall
  obtain ⟨O,G,A,ψ,hO,hG,hSphere,hKnown,hDir,hAdj,hSmooth,hRep,hBound⟩ := hp hpos δ hδ hSmall
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  obtain ⟨hr,hBack,hNormal,_⟩ := hS hpos δ hδ A
  let D : Set (X dim) := {z : (X dim) | lam • z ∈ Ω}
  have hD : IsOpen D := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hγ : SmoothMetric univ d.γ :=
    ⟨fun i j => (contDiff_depthScale (normal := normal) 4).contDiffOn.mul ((smoothMetric_dilatedMetric hg₁ lam).1 i j),
      fun y _ => (hg₁.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)⟩
  have he y (hy : y ∈ Y) := hBack.2.2.2.2.2.2.2 y (hYO hy)
  have hec (i : (I dim)) := (hBack.2.2.2.2.2.2.1 i).continuousOn.mono hYO
  have hElam : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hrD : ContDiff ℝ ∞ d.radius := contDiff_shrinkingRadius (contDiff_conformalDepth (normal := normal) 4) R p δ
  have hFlux {u v : (X dim) → ℝ} (hu : Harmonic D d.g₁ u) (hv : Harmonic D d.g₂ v)
      (heq : EqOn u v {y | lam • y ∈ W}) :
      EqOn (fun y => normalSphereGreenFlux d.g₁ d.expMap d.frame d.radius G y u) v Y :=
    cylinderGreenFlux_reproduces hn hΩ hg₁ hg₂ hγ hG₁ hpos (hRooms hpos).1 (hRooms hpos).2
      hElam hNormal hY' hrD.continuous.continuousOn (fun y hy => ⟨(hr y hy).1,(hr y hy).2.1⟩)
      he hec hO hG hSphere hKnown hu hv heq
  have hValue {u v : (X dim) → ℝ} (hu : Harmonic D d.g₁ u) (hv : Harmonic D d.g₂ v)
      (heq : EqOn u v {y | lam • y ∈ W}) : EqOn (transferValue d (complexDensity ψ) u) v Y := by
    intro y hy
    have hBall := harmonicOnBall_of_normalCoordinates hD (hNormal.mono_ambient (hRooms hpos).1)
      hy (hr y hy).1.le (hr y hy).2.1.le hu
    exact (hRep y hy u hBall).trans (hFlux hu hv heq hy)
  have hOne (g : (MetricField dim)) := harmonic_one D g
  have hmass (y : (X dim)) (hy : y ∈ Y) : sphereAverage d.frame y (fun w => complexDensity ψ (y,w)) = 1 := by
    have h := hValue (hOne d.g₁) (hOne d.g₂) (fun _ _ => rfl) hy
    change (∫ w : ↥(standardSphere dim), (ψ (y,frameVector d.frame y w) : ℂ) ∂(sphereProbability dim)) = 1
    rw [integral_complex_ofReal]
    rw [show (∫ w : ↥(standardSphere dim), ψ (y,frameVector d.frame y w) ∂(sphereProbability dim)) = 1 from
      by simpa only [transferValue,complexDensity,Complex.ofReal_re,mul_one] using h]
    rfl
  have hSmooth' : smoothNear (complexDensity ψ) (bundle Y d.γ) := by
    obtain ⟨S,hS,hSub,hψ⟩ := hSmooth
    exact ⟨S,hS,hSub,Complex.ofRealCLM.contDiff.comp_contDiffOn hψ⟩
  have hg₁Ω := smoothMetric_restrict hg₁ (subset_univ Ω)
  have hg₂Ω := smoothMetric_restrict hg₂ (subset_univ Ω)
  let v₁ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam
  let v₂ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam
  have hAffine (i : (I dim)) := hValue (harmonicCoordinates_dilated hΩ hg₁Ω hchart₁ lam i)
    (harmonicCoordinates_dilated hΩ hg₂Ω hchart₂ lam i) (fun _ _ => rfl)
  have hpairs (a : Fin n) : EqOn (transferValue d (complexDensity ψ) (v₁ a)) (v₂ a) Y := by
    apply hValue (harmonic_renormalizedHarmonic hΩ hg₁Ω hchart₁ (hu₁ a) _ _ hpos.ne')
      (harmonic_renormalizedHarmonic hΩ hg₂Ω hchart₂ (hu₂ a) _ _ hpos.ne')
    intro y hy
    simp only [renormalizedHarmonic,hpair a hy]
  refine ⟨A,complexDensity ψ,hDir,hAdj,⟨hSmooth',hmass,hAffine,hpairs,hFloor hpos,?_,hBound⟩⟩
  exact fun a y hy w => hTaylor hpos δ hδ A a y hy w

end CalderonN
