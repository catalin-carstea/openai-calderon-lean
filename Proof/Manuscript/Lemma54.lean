module

public import Proof.CalderonN.ChartTransferAssembly
public import Proof.CalderonN.ConformalActualGreenTransfer
public import Proof.CalderonN.SmoothMetricFrame

import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.ConformalGreenDensityEstimate
import Proof.CalderonN.ConformalGreenDensityJets
import Proof.CalderonN.ShrinkingRadiusParameter
import Proof.CalderonN.SpectralTransferFacts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

noncomputable section

open CalderonN Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]

/-- The cutoff-weighted function is its mean-zero part plus the constant fiber. -/
private theorem fiberSq_cutoff_le (d : Data dim) (ψ : Field dim) (χ : X dim → ℝ) (y : X dim)
    (hψ : MemLp (fun w : ↥(standardSphere dim) => ψ (y, frameVector d.frame y w))
      2 (sphereProbability dim)) :
    fiberSq d.frame y (fun w => (χ y : ℂ) * ψ (y, w)) ≤
      2 * (fiberSq d.frame y (fun w => cutoffDensity χ ψ (y, w)) + χ y ^ 2) := by
  let u (w : ↥(standardSphere dim)) := (χ y : ℂ) * ψ (y, frameVector d.frame y w)
  let v (w : ↥(standardSphere dim)) := cutoffDensity χ ψ (y, frameVector d.frame y w)
  have hu : MemLp u 2 (sphereProbability dim) := hψ.const_mul (χ y : ℂ)
  have hv : MemLp v 2 (sphereProbability dim) := (hψ.sub (memLp_const 1)).const_mul (χ y : ℂ)
  have hpoint (w : ↥(standardSphere dim)) :
      ‖u w‖ ^ 2 ≤ 2 * (‖v w‖ ^ 2 + χ y ^ 2) := by
    have he : u w = v w + (χ y : ℂ) := by simp only [u, v, cutoffDensity]; ring
    rw [he]
    have h := norm_add_le (v w) (χ y : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) h 2, sq_abs (χ y),
      sq_nonneg (‖v w‖ - |χ y|)]
  have huI := hu.norm.integrable_sq
  have hvI := hv.norm.integrable_sq
  have hi := integral_mono huI ((hvI.add (integrable_const (χ y ^ 2))).const_mul 2) hpoint
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hvI (integrable_const (χ y ^ 2)), integral_const, probReal_univ, one_smul] at hi
  rw [fiberSq_eq_integral_norm_sq, fiberSq_eq_integral_norm_sq]
  change (∫ w, ‖u w‖ ^ 2 ∂sphereProbability dim) ≤
    2 * ((∫ w, ‖v w‖ ^ 2 ∂sphereProbability dim) + χ y ^ 2)
  exact hi

omit [NeZero dim] in
private theorem exists_cylinder_volume_ceiling (normal : I dim) {g : MetricField dim}
    (hg : SmoothMetric univ g) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
      chartVolume (conformalReference (depthScale normal 4) g lam) y ≤ V := by
  let γ (q : ℝ × X dim) := conformalReference (depthScale normal 4) g q.1 q.2
  let T := Icc (0 : ℝ) 1 ×ˢ coordinateCylinder normal
  have hT : IsCompact T := isCompact_Icc.prod (isCompact_coordinateCylinder (normal := normal))
  have hγ (i j : I dim) : ContDiffOn ℝ ∞ (fun q => γ q i j) univ := by
    have hDepth := (contDiff_depthScale (normal := normal) 4).comp
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × X dim → X dim))
    have hmet := (contDiffOn_univ.mp (hg.1 i j)).comp
      (contDiff_fst.smul contDiff_snd : ContDiff ℝ ∞ (fun q : ℝ × X dim => q.1 • q.2))
    exact (hDepth.mul hmet).contDiffOn
  have hvol : ContinuousOn (fun q => Real.sqrt (γ q).det) T :=
    ((Real.continuous_sqrt.comp_continuousOn
      (contDiffOn_det_of_entries hγ).continuousOn).mono (subset_univ T))
  obtain ⟨B, hB⟩ := hT.bddAbove_image hvol
  refine ⟨max B 0, le_max_right _ _, fun lam hlam y hy => ?_⟩
  exact (hB (mem_image_of_mem (fun q => Real.sqrt (γ q).det)
    (show (lam, y) ∈ T from ⟨hlam, hy⟩))).trans (le_max_left _ _)

end CalderonPaper

public section

open CalderonN CalderonN.FixedTube CalderonN.MovingSphere Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Lemma 5.4 of the pinned manuscript. The exact conormal density of
the continued Green kernel on the same moving spheres is uniformly
bounded after multiplication by the fixed base cutoff. -/
theorem lemma54 (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p)
    {ρ R ε tb K c₀ floor ε₀ C : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (htb : 0 < tb) (hK : 0 < K) (hfloor : 1 ≤ floor) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1 / 4)
    (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let χ := cylinderCutoff normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        let e := fun y : X dim => smoothMetricFrame (γ y)
        Small Y γ q₂ r ε →
        ∃ (O : Set (X dim × X dim)) (G : X dim × X dim → ℝ),
          IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
          (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (endpoint (E lam) r (y, frameVector e y w), y) ∈ O) ∧
          EqOn G (dilatedInitialGreen W G₁ G₂ lam)
            (lowerNormalSeed normal (normalPairDomain (interior Z) γ ρ (E lam))) ∧
          let ψ := movingGreenFluxDensity γ q₁ (E lam) e r G
          Real.sqrt (outputSq Y γ e (fun q => (χ q.1 : ℂ) * (ψ q : ℂ))) ≤ D := by
  let Y := interior (coordinateCylinder normal)
  let U := ball (0 : X dim) 3
  let χ := cylinderCutoff normal 4 tb
  have hYZ : Y ⊆ interior Z := interior_subset.trans hCZ
  have hYU : Y ⊆ U := interior_subset.trans
    (coordinateCylinder_subset_closedBall.trans (closedBall_subset_ball (by norm_num)))
  have hN (lam : ℝ) (hlam : lam ∈ Icc (-1 : ℝ) 1) :=
    (hNormal lam hlam).mono_centers (interior_subset : interior Z ⊆ Z)
  have hRcap δ (hδ : δ ∈ Ioc (0 : ℝ) 1) y (hy : y ∈ Y) :=
    hRadius δ hδ y (interior_subset (hYZ hy))
  have hp' : 1 ≤ p := by omega
  have hJets := uniformCylinderGreenDensityJets_of_scaledData hg₁ hg₂ hE hCZ
    hp' hρ hR hε hN hRcap hData
  obtain ⟨B, hB, hTrace⟩ := uniformActualCylinderGreenTraceBound_of_densityJets hg₁ hg₂ hE
    isOpen_interior hCZ hp' hρ hR hε hN hRcap hJets
  obtain ⟨V, hV, hVol⟩ := exists_cylinder_volume_ceiling normal hg₁
  let H := ∫ y in Y, χ y ^ 2
  have hχ : ContDiff ℝ ∞ χ := contDiff_cylinderCutoff (normal := normal) 4 tb
  have hχc : HasCompactSupport χ := hasCompactSupport_cylinderCutoff htb hdepth
  have hχY : tsupport χ ⊆ Y := cylinderCutoff_tsupport_subset_interior htb hdepth
  have hχsq : HasCompactSupport (fun y => χ y ^ 2) :=
    hχc.mono (fun y hy hz => hy (by simp [hz]))
  have hχint : IntegrableOn (fun y => χ y ^ 2) Y :=
    ((hχ.continuous.pow 2).integrable_of_hasCompactSupport hχsq).integrableOn
  let D := Real.sqrt (2 * ((C * B) ^ 2 + V * H))
  refine ⟨D, Real.sqrt_nonneg _, ?_⟩
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hTrace, hSetup, eventually_cylinder_green_chart hΩ hside, hI] with
    lam htrace hlam hRooms hlamI hpos δ hδ
  dsimp only
  intro hSmall
  obtain ⟨O, G, hO, hG, hSphere, hKnown, hNormBound⟩ := htrace hpos δ hδ hSmall
  let γ := conformalReference (depthScale normal 4) g₁ lam
  let g := dilatedMetric g₁ lam
  let q₂ := dilatedMetric g₂ lam
  let r := shrinkingRadius R p (conformalDepth normal 4) δ
  let e (y : X dim) := smoothMetricFrame (γ y)
  let A := actualMovingTraceAdjoint γ g (E lam) e r
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  let ψR := movingGreenFluxDensity γ g (E lam) e r G
  let ψ : Field dim := complexDensity ψR
  obtain ⟨hrad, hBack, hNormalY, hProf⟩ := hlam hpos δ hδ A
  have hγ : SmoothMetric univ γ :=
    ⟨fun i j => (contDiff_depthScale (normal := normal) 4).contDiffOn.mul
      ((smoothMetric_dilatedMetric hg₁ lam).1 i j),
      fun y _ => (hg₁.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)⟩
  have he (i : I dim) : ContDiff ℝ ∞ (fun y => e y i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame hγ.1 hγ.2 i)
  have hFrame y (hy : y ∈ Y) := hBack.2.2.2.2.2.2.2 y (hYU hy)
  have hE' : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius
    (contDiff_conformalDepth (normal := normal) 4) R p δ
  have hrY y (hy : y ∈ Y) : 0 < r y ∧ r y < ρ := ⟨(hrad y hy).1, (hrad y hy).2.1⟩
  obtain ⟨hDir, hAdj, hψR, hFlux, _⟩ := actualGreenTransfer (Y := Y) (Ω := U)
    isOpen_interior isOpen_ball hγ (smoothMetric_dilatedMetric hg₁ lam)
    (smoothMetric_dilatedMetric hg₂ lam) hE' hNormalY he hFrame hr hrY hO hG hSphere
  have hψ : smoothNear ψ (bundle Y γ) := by
    obtain ⟨S, hS, hSub, hSmooth⟩ := hψR
    exact ⟨S, hS, hSub, Complex.ofRealCLM.contDiff.comp_contDiffOn hSmooth⟩
  let Ulam : Set (X dim) := {y | lam • y ∈ Ω}
  have hRepOne :=
    cylinderGreenFlux_reproduces hn hΩ hg₁ hg₂ hγ hG₁ hpos (hRooms hpos).1 (hRooms hpos).2
      hE' hNormalY hYZ hr.continuous.continuousOn hrY hFrame
      (fun i => (he i).continuous.continuousOn) hO hG hSphere hKnown
      (harmonic_one Ulam g) (harmonic_one Ulam q₂) (fun _ _ => rfl)
  have hmean (y : X dim) (hy : y ∈ Y) :
      sphereAverage e y (fun w => ψ (y, w)) = 1 := by
    have hu : HarmonicOnBall g (closedBallImage γ (E lam) r y) (fun _ => 1) :=
      ⟨⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩,
        fun x _ => (harmonic_one univ g).2 x (mem_univ _)⟩
    have hm := (hFlux y hy (fun _ => 1) hu).trans (hRepOne hy)
    change (∫ w : ↥(standardSphere dim),
      (ψR (y, frameVector e y w) : ℂ) ∂(sphereProbability dim)) = 1
    rw [integral_complex_ofReal]
    simpa only [mul_one, Complex.ofReal_one] using congrArg Complex.ofReal hm
  have hAd : Admissible Y U K ρ c₀ M Cj floor ε d :=
    ⟨hBack, hNormalY.max_radius_of_le (fun y hy => (hrad y hy).2.1.le),
      hDir, hAdj, hProf, hSmall⟩
  let φ := cutoffDensity χ ψ
  have htest := cutoffDensity_test hψ hχ hχc hχY hFrame hmean
  have hEll : Elliptic Y K d.γ :=
    ⟨fun i j => (hBack.1.1 i j).mono hYU, fun y hy => hBack.1.2 y (hYU hy)⟩
  obtain ⟨hParseval, hSum, hEnergyInt⟩ := htest.spectralTransferFacts hn isOpen_interior
    d hEll hK hFrame (fun i => (he i).contDiffOn) hProf hfloor
  have hEnergy := cutoffDensity_energy_bound hC hEstimate hε hε₀ hAd
    hψ hχ hχc hχY hmean hYU hNormBound
  have hEnergySq : energySq Y d.γ d.frame d.radius φ ≤ (C * B) ^ 2 :=
    (Real.sqrt_le_iff.mp hEnergy).2
  have hlam' : lam ∈ Icc (0 : ℝ) 1 := ⟨hpos.le, hlamI.2⟩
  have hpoint y (hy : y ∈ Y) :
      chartVolume d.γ y * fiberSq d.frame y (fun w => (χ y : ℂ) * ψ (y, w)) ≤
        2 * (sphereEnergyDensity d φ y + V * χ y ^ 2) := by
    let : CompactSpace ↥(standardSphere dim) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
    have hLp := (continuous_frame_density hψ hy (hFrame y hy)).memLp_of_hasCompactSupport
      (p := 2) (μ := sphereProbability dim) (HasCompactSupport.of_compactSpace _)
    have hvol0 : 0 ≤ chartVolume d.γ y := Real.sqrt_nonneg _
    have hcut := mul_le_mul_of_nonneg_left (fiberSq_cutoff_le d ψ χ y hLp) hvol0
    have hdom := mul_fiberSq_le_energyDensity d φ y (chartVolume d.γ y) hvol0 le_rfl
      (hfloor.trans ((hProf.2 y hy).2.1)) (hParseval y hy) (hSum y hy)
    have hv := mul_le_mul_of_nonneg_right (hVol lam hlam' y (interior_subset hy)) (sq_nonneg (χ y))
    calc
      _ ≤ chartVolume d.γ y * (2 * (fiberSq d.frame y (fun w => φ (y, w)) + χ y ^ 2)) := hcut
      _ = 2 * (chartVolume d.γ y * fiberSq d.frame y (fun w => φ (y, w)) +
          chartVolume d.γ y * χ y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hdom hv) (by norm_num)
  let U₀ (q : X dim × X dim) := (χ q.1 : ℂ) * ψ q
  have hIntegral : outputSq Y d.γ d.frame U₀ ≤ 2 * ((C * B)^2 + V * H) := by
    change (∫ y in Y, chartVolume d.γ y * fiberSq d.frame y (fun w => U₀ (y, w))) ≤ _
    calc
      _ ≤ ∫ y in Y, 2 * (sphereEnergyDensity d φ y + V * χ y ^ 2) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => mul_nonneg (Real.sqrt_nonneg _)
            (fiberSq_nonneg _ _ _)))
          ((hEnergyInt.add (hχint.const_mul V)).const_mul 2) ?_
        exact (ae_restrict_iff' isOpen_interior.measurableSet).mpr
          (Filter.Eventually.of_forall hpoint)
      _ = 2 * (energySq Y d.γ d.frame d.radius φ + V * H) := by
        rw [integral_const_mul, integral_add hEnergyInt (hχint.const_mul V), integral_const_mul]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hEnergySq le_rfl) (by norm_num)
  exact ⟨O, G, hO, hG, hSphere, hKnown, Real.sqrt_le_sqrt hIntegral⟩

end CalderonPaper
