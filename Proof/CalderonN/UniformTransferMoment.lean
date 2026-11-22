module

public import Proof.CalderonN.CoerciveTransferMoment
public import Proof.CalderonN.SphereCoercivity

import Mathlib.Tactic
import Proof.CalderonN.SpectralTransferFacts

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- (Data dim) required of the transfer producer, for the specified sphere
family. All estimates use the same density and the same fixed cutoff. -/
structure SphereTransferBounds (Y : Set (X dim)) (d : (Data dim)) (ψ : (Field dim)) (χ : (X dim) → ℝ)
    {n : ℕ} (u₁ u₂ : Fin n → (X dim) → ℝ) (Ctay volFloor B : ℝ) : Prop where
  smooth : smoothNear ψ (bundle Y d.γ)
  mean : ∀ y ∈ Y, sphereAverage d.frame y (fun w => ψ (y,w)) = 1
  affine : ∀ i : (I dim), EqOn (transferValue d ψ (fun x => x i)) (fun x => x i) Y
  pairs : ∀ a, EqOn (transferValue d ψ (u₁ a)) (u₂ a) Y
  volume : ∀ y ∈ Y, volFloor ≤ chartVolume d.γ y
  remainder : ∀ a y, y ∈ Y → ∀ w : ↥(standardSphere dim),
    let z := endpoint d.expMap d.radius (y,frameVector d.frame y w)
    |u₁ a z - (u₁ a y + fderiv ℝ (u₁ a) y (z-y))| ≤ Ctay * (d.radius y)^2
  residual : traceNorm Y d (cutoffDensity χ ψ) ≤ B

/-- The literal uniform moment estimate, with its constants chosen
before dilation, regularization, and the index of the harmonic pair. -/
theorem exists_uniform_weighted_moment_of_sphereTransfer (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hYΩ : Y ⊆ Ω)
    {g₁ g₂ : (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {p : ℕ} {R ε : ℝ}
    {K ρ c₀ C floor ε₀ : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hε : 0 ≤ ε) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C) (hK : 0 < K) (hfloor : 1 ≤ floor)
    (hEst : UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C)
    (hSetup : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : (TraceAdjoint dim),
      let d := conformalSphereData normal g₁ g₂ E p R lam δ A
      (∀ y ∈ Y, d.radius y ≤ ρ) ∧
      Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
      NormalCoordinates Y Ω d.γ d.expMap (fun _ => ρ) ∧
      Profile Y d.γ d.frame d.radius floor c₀ Cj)
    {χ : (X dim) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχY : tsupport χ ⊆ Y)
    {n : ℕ} (u₁ u₂ : ℝ → Fin n → (X dim) → ℝ)
    (hu : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ a, ContinuousOn (u₁ lam a) Ω ∧
      ContinuousOn (u₂ lam a) Y)
    (htransfer : ∃ Ctay volFloor B : ℝ, 0 ≤ Ctay ∧ 0 < volFloor ∧ 0 ≤ B ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1,
        Small Y (conformalReference (depthScale normal 4) g₁ lam) (dilatedMetric g₂ lam)
          (shrinkingRadius R p (conformalDepth normal 4) δ) ε →
        ∃ (A : (TraceAdjoint dim)) (ψ : (Field dim)),
          let d := conformalSphereData normal g₁ g₂ E p R lam δ A
          Dirichlet Y d.γ d.g₁ d.expMap d.radius ∧
          IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint ∧
          SphereTransferBounds Y d ψ χ (u₁ lam) (u₂ lam) Ctay volFloor B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1,
      Small Y (conformalReference (depthScale normal 4) g₁ lam) (dilatedMetric g₂ lam)
        (shrinkingRadius R p (conformalDepth normal 4) δ) ε →
      ∀ a, eLpNorm (fun y => χ y * (u₂ lam a y-u₁ lam a y) /
        (shrinkingRadius R p (conformalDepth normal 4) δ y)^2) 2
        ((volume : Measure (X dim)).restrict Y) ≤ ENNReal.ofReal D := by
  obtain ⟨Ctay,volFloor,B,hCtay,hvolFloor,hB,hTransfer⟩ := htransfer
  let H := ∫ y in Y, χ y^2
  have hH : 0 ≤ H := integral_nonneg fun y => sq_nonneg (χ y)
  let D := Real.sqrt (2*Ctay^2 * ((C*B)^2/volFloor + H))
  refine ⟨D,Real.sqrt_nonneg _,?_⟩
  filter_upwards [hSetup,hu,hTransfer] with lam hlam hU hφ hpos δ hδ hSmall a
  obtain ⟨A,ψ,hDir,hAdj,hBound⟩ := hφ hpos δ hδ hSmall
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  obtain ⟨hrad,hBack,hN,hProf⟩ := hlam hpos δ hδ A
  have hd : Admissible Y Ω K ρ c₀ M Cj floor ε d :=
    ⟨hBack,hN.max_radius_of_le hrad,hDir,hAdj,hProf,hSmall⟩
  obtain ⟨hγ,_,_,_,_,_,he,hframe⟩ := hBack
  have hγY : Elliptic Y K d.γ :=
    ⟨fun i j => (hγ.1 i j).mono hYΩ,fun y hy => hγ.2 y (hYΩ hy)⟩
  have hframeY y (hy : y ∈ Y) := hframe y (hYΩ hy)
  have htest := cutoffDensity_test hBound.smooth hχ hχc hχY hframeY hBound.mean
  obtain ⟨hParseval,hSum,hIntegrable⟩ :=
    htest.spectralTransferFacts hn hY d hγY hK hframeY (fun i => (he i).mono hYΩ) hProf hfloor
  exact weighted_pair_moment_of_coercivity hY hYΩ hC hfloor hEst hε hε₀ hd
    hBound.smooth hχ hχc hχY (hU hpos a).1 (hU hpos a).2 hBound.mean hBound.affine
    (hBound.pairs a) Ctay volFloor B H hCtay hvolFloor hB hH hBound.volume
    (hBound.remainder a) hParseval hSum hIntegrable le_rfl hBound.residual

end CalderonN
