module

public import Proof.Manuscript.TransferDensity
public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.Radius
public import Proof.CalderonN.MovingSphere.RadiusSeed
public import Proof.CalderonN.SmoothMetricFrame

import Proof.Manuscript.LocalGreenChart
import Proof.Manuscript.SphereChartLocality
import Proof.Manuscript.UpperGreenMixedJets
import Proof.Manuscript.LowerGreen.FramedPhysicalGreenGerms
import Proof.Manuscript.LowerGreen.ShrinkingRadiusBaseDerivative
import Proof.Manuscript.LowerGreen.UniformNormalizedBallPoisson
import Proof.Manuscript.LowerGreen.LowerPhysicalPoisson
import Proof.CalderonN.ActualGreenTransfer
import Proof.CalderonN.LocalNormalGreenFlux
import Proof.CalderonN.CylinderGreenReproduction
import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.SphereCoercivity
import Proof.CalderonN.RadiusProfileGeometry
import Proof.CalderonN.MovingTraceBackgroundBounds
import Proof.CalderonN.ScaledGreenDatumJets
import all Proof.CalderonN.Coordinates
import Mathlib.Tactic

public section

open Set Filter Metric MeasureTheory CalderonN
open CalderonN.FixedTube CalderonN.MovingSphere CalderonPaper.SphereLocality CalderonPaper.LowerGreen
open scoped ContDiff Topology

namespace CalderonPaper

set_option maxHeartbeats 8000000 in
/-- Proposition 4.3 for the continued kernel of the shrinking-sphere
construction, using the same kernel in the flux and the seed agreements. -/
theorem proposition43
    {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {a : ℕ} {u₁ u₂ : Fin a → X n → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W)
    {p : ℕ} (hp : 2 ≤ p) {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 < ε) (htb : 0 < tb)
    {E : ℝ → (X n) × (X n) → X n}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => E q.1 q.2))
    {lam₀ : ℝ} (hlam₀ : 0 < lam₀)
    (hNormal : ∀ lam ∈ Icc (-lam₀) lam₀,
      NormalCoordinates (closedBall (0 : X n) (5/2)) (ball (0 : X n) 3)
        (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    (ht : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1/4)
    {d : ℝ} (hd : 0 < d)
    (mixedKernel : ℝ → ℝ → (X n) × (X n) → ℝ)
    (continuation :
      let Y := interior (coordinateCylinder normal)
      let Z := closedBall (0 : X n) (5/2)
      let t := conformalDepth normal 4
      let γ := conformalReference (depthScale normal 4) g₁
      let r := shrinkingRadius R p t
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        ball (0 : X n) 3 ⊆ {y | lam • y ∈ Ω} ∧
        ∃ (O₀ : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ),
          IsOpen O₀ ∧ fixedSeparationSet 4 (d/2) ⊆ O₀ ∧
          ProductSolutionOn q₁ q₂ O₀ F ∧ (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ C₀) ∧
          ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) q₂ (r δ) ε →
            let G := mixedKernel lam δ
            ∃ O : Set ((X n) × (X n)),
              IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
              lowerNormalSeed normal N ⊆ O ∧
              EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
              (∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r δ) w, w.1) ∈ O) ∧
              (∀ w ∈ bundle Y (γ lam), tb < t w.1 →
                let q := (endpoint (E lam) (r δ) w, w.1)
                q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) ∧
              ∀ w ∈ bundle Y (γ lam), w.1 normal < -(1/4 : ℝ) →
                let q := (endpoint (E lam) (r δ) w, w.1)
                ‖q.1‖ ≤ 3 ∧ ‖q.2‖ ≤ 3 ∧ G =ᶠ[𝓝 q] dilatedGreen G₁ lam) :
    let Y := interior (coordinateCylinder normal)
    let t := conformalDepth normal 4
    let γ := conformalReference (depthScale normal 4) g₁
    let r := shrinkingRadius R p t
    let χ := cylinderCutoff normal 4 tb
    ∃ C : ℕ → ℝ, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let q₁ := dilatedMetric g₁ lam
      let q₂ := dilatedMetric g₂ lam
      let e : Frame n := fun y => smoothMetricFrame (γ lam y)
      ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) q₂ (r δ) ε →
        ∃ (O : Set ((X n) × (X n))) (ψ : (X n) × (X n) → ℝ),
          let G := mixedKernel lam δ
          let T := densityValue (E lam) e (r δ) ψ
          let N := normalPairDomain (interior (closedBall (0 : X n) (5/2))) (γ lam) ρ (E lam)
          IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
          lowerNormalSeed normal N ⊆ O ∧ EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
          (∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r δ) w, w.1) ∈ O) ∧
          smoothNear ψ (bundle Y (γ lam)) ∧
          (∀ y ∈ Y, ∀ u, HarmonicOnBall q₁ (closedBallImage (γ lam) (E lam) (r δ) y) u →
            T u y = normalSphereGreenFlux q₁ (E lam) e (r δ) G y u) ∧
          (∀ y₀ ∈ Y, ∀ U : Set (X n), IsOpen U → ∀ u, Harmonic U q₁ u →
            closedBallImage (γ lam) (E lam) (r δ) y₀ ⊆ U →
            ∃ V : Set (X n), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ Y ∧
              (∀ y ∈ V, closedBallImage (γ lam) (E lam) (r δ) y ⊆ U) ∧ Harmonic V q₂ (T u)) ∧
          (∀ y ∈ Y,
            (∫ w : ↥(standardSphere n), ψ (y, frameVector e y w) ∂(sphereProbability n)) = 1 ∧
            (∀ i : I n, T (fun x => x i) y = y i) ∧
            ∀ i : Fin a, T (fun x => u₁ i (lam • x)) y = u₂ i (lam • y)) ∧
          ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere n), angularBaseJetBound e ψ y w C := by
  let Y := interior (coordinateCylinder normal)
  let Z := closedBall (0 : X n) (5/2)
  let B := ball (0 : X n) 3
  let t := conformalDepth normal 4
  let γ := conformalReference (depthScale normal 4) g₁
  let q₁ := dilatedMetric g₁
  let q₂ := dilatedMetric g₂
  let r := shrinkingRadius R p t
  let χ := cylinderCutoff normal 4 tb
  obtain ⟨c, g₁', g₂', hc, hDΩ, hside', hg₁', hg₂', he₁, he₂, hG₁', _, _, _⟩ :=
    exists_global_alignedGreen_chart hΩ hside hg₁ hg₂ hG₁ hG₂ hmetric hgreen
  let D := ball (0 : X n) c
  let W' := W ∩ D
  let γ' := conformalReference (depthScale normal 4) g₁'
  let q₁' := dilatedMetric g₁'
  let q₂' := dilatedMetric g₂'
  let e (lam : ℝ) : Frame n := fun y => smoothMetricFrame (γ lam y)
  let e' (lam : ℝ) : Frame n := fun y => smoothMetricFrame (γ' lam y)
  let ψ (lam δ : ℝ) := movingGreenFluxDensity (γ' lam) (q₁' lam) (E lam) (e' lam) (r δ)
    (mixedKernel lam δ)
  have hZB : Z ⊆ B := closedBall_subset_ball (by norm_num)
  have hCY : coordinateCylinder normal ⊆ interior Z :=
    (coordinateCylinder_subset_closedBall (normal := normal)).trans
      ((closedBall_subset_ball (by norm_num)).trans
        (isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall))
  have hYZ : Y ⊆ interior Z := interior_subset.trans hCY
  have hYB : Y ⊆ B := hYZ.trans (interior_subset.trans hZB)
  have hDopen : IsOpen D := isOpen_ball
  have hBopen : IsOpen B := isOpen_ball
  have hYopen : IsOpen Y := isOpen_interior
  obtain ⟨C₀,hC₀,hCont⟩ := continuation
  let a₀ := min lam₀ (min 1 (c/10))
  let S := Icc (-a₀) a₀
  have ha₀ : 0 < a₀ := lt_min hlam₀ (lt_min zero_lt_one (by positivity))
  have hI : S ∈ 𝓝 (0:ℝ) := Icc_mem_nhds (neg_lt_zero.mpr ha₀) ha₀
  have hS₁ : S ⊆ Icc (-1 : ℝ) 1 := by
    intro lam hlam
    have h : a₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    exact ⟨(neg_le_neg h).trans hlam.1,hlam.2.trans h⟩
  have hS₀ : S ⊆ Icc (-lam₀) lam₀ := by
    intro lam hlam
    have h : a₀ ≤ lam₀ := min_le_left _ _
    exact ⟨(neg_le_neg h).trans hlam.1,hlam.2.trans h⟩
  have hDil₅ (lam : ℝ) (hlam : lam ∈ S) (z : X n) (hz : z ∈ closedBall (0 : X n) 5) :
      lam • z ∈ D := by
    have hAbs : |lam| ≤ c/10 := (abs_le.mpr hlam).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hAbs (mem_closedBall_zero_iff.mp hz) (norm_nonneg _) (by positivity)).trans_lt
      (by linarith)
  have hB_subset₅ : B ⊆ closedBall (0 : X n) 5 :=
    (ball_subset_ball (by norm_num)).trans ball_subset_closedBall
  have hγS (lam : ℝ) (hlam : lam ∈ S) : EqOn (γ' lam) (γ lam) B :=
    fun z hz => congrArg (depthScale normal 4 z • ·) (he₁ (hDil₅ lam hlam z (hB_subset₅ hz)))
  have hNormalS (lam : ℝ) (hlam : lam ∈ S) :
      NormalCoordinates Z B (γ' lam) (E lam) (fun _ => ρ) :=
    normalCoordinates_congrOn hBopen hZB (hγS lam hlam).symm (hNormal lam (hS₀ hlam))
  have hγfam (i j : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => γ' q.1 q.2 i j) := by
    exact ((contDiff_depthScale (normal := normal) 4).comp contDiff_snd).mul
      ((contDiffOn_univ.mp (hg₁'.1 i j)).comp (contDiff_fst.smul contDiff_snd))
  have hγpos (lam : ℝ) (y : X n) : (γ' lam y).PosDef :=
    (hg₁'.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)
  have hFrameFam (i : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => e' q.1 q.2 i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame
      (fun i j => (hγfam i j).contDiffOn) (fun q _ => hγpos q.1 q.2) i)
  have hFrameOn (lam : ℝ) (_ : lam ∈ S) (y : X n) (_ : y ∈ coordinateCylinder normal) (i j : I n) :
      metricPair (γ' lam) y (e' lam y i) (e' lam y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγpos lam y) i j
  obtain ⟨D₀,hD₀,hDjet⟩ := exists_uniform_shrinkingRadius_baseDerivative
    (isCompact_coordinateCylinder (normal := normal))
    (contDiff_conformalDepth (normal := normal) 4) hR.le (p := p)
  have hKU : coordinateCylinder normal ⊆ Z := hCY.trans interior_subset
  choose CU hCU hUpper using (fun k =>
    exists_uniform_upper_movingGreen_mixed_jets (Y := Y) k hg₁' hg₂' hγfam hγpos hE hFrameFam
      isCompact_Icc (isCompact_coordinateCylinder (normal := normal)) hS₁
      hYopen interior_subset hKU hρ hd hD₀ hC₀ hNormalS hFrameOn)
  have hqfam (i j : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => q₁' q.1 q.2 i j) :=
    ((contDiffOn_univ.mp (hg₁'.1 i j)).comp (contDiff_fst.smul contDiff_snd))
  have hqpos (lam : ℝ) (z : X n) : (q₁' lam z).PosDef := hg₁'.2 _ (mem_univ _)
  obtain ⟨A,WBall,CL,PL,hJV,hWBall,hBW,hAW,hPL,hRepL,hJetL⟩ :=
    exists_uniform_normalizedBallPoisson_jets hqfam hqpos hE hFrameFam
      isCompact_Icc (isCompact_coordinateCylinder (normal := normal)) hKU hρ hD₀ hNormalS hFrameOn
  let C (k : ℕ) := max (CL k) (CU k)
  have hLow := eventually_dilated_mem_side_of_negative_coordinate hside' 3 (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨C,?_⟩
  dsimp only
  filter_upwards [hI,hCont,hLow] with lam hlam hContL hLowL hpL
  intro δ hδ hSmall
  obtain ⟨_,O₀,F,hO₀,hFroom,hF,hFB,hSweep⟩ := hContL hpL
  obtain ⟨O,hO,hG,hNseed,hSeed,hCover,hTop,hBottom⟩ := hSweep δ hδ hSmall
  let G := mixedKernel lam δ
  let DL : Set (X n) := {x | lam • x ∈ D}
  let O' := O ∩ (B ×ˢ B)
  have hB₃ : B ⊆ DL := fun z hz => hDil₅ lam hlam z (hB_subset₅ hz)
  have hDL : IsOpen DL :=
    hDopen.preimage (show Continuous (fun x : X n => lam • x) from
      (continuous_id : Continuous (id : X n → X n)).const_smul lam)
  have hq₁DL : EqOn (q₁' lam) (q₁ lam) DL := fun _ hx => he₁ hx
  have hq₂DL : EqOn (q₂' lam) (q₂ lam) DL := fun _ hx => he₂ hx
  have hq₁B : EqOn (q₁' lam) (q₁ lam) B := hq₁DL.mono hB₃
  have hq₂B : EqOn (q₂' lam) (q₂ lam) B := hq₂DL.mono hB₃
  have hγB : EqOn (γ' lam) (γ lam) B := fun x hx => congrArg (depthScale normal 4 x • ·) (hq₁B hx)
  have heqFrame (y : X n) (hy : y ∈ B) : e' lam y = e lam y :=
    congrArg smoothMetricFrame (hγB hy)
  have hE' : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hNormalZ : NormalCoordinates Z B (γ' lam) (E lam) (fun _ => ρ) := hNormalS lam hlam
  have hNormalY : NormalCoordinates Y B (γ' lam) (E lam) (fun _ => ρ) :=
    hNormalZ.mono_centers (hYZ.trans interior_subset)
  have hγs : SmoothMetric univ (γ' lam) :=
    ⟨fun i j => (contDiff_depthScale (normal := normal) 4).contDiffOn.mul
        ((smoothMetric_dilatedMetric hg₁' lam).1 i j),
      fun y _ => (hg₁'.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)⟩
  have hsFrame (i : I n) : ContDiff ℝ ∞ (fun y => e' lam y i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame hγs.1 hγs.2 i)
  have hFrame (y : X n) (_hy : y ∈ Y) (i j : I n) :
      metricPair (γ' lam) y (e' lam y i) (e' lam y j) = if i = j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγs.2 y (mem_univ _)) i j
  have hRadius' (y : X n) (hy : y ∈ Y) : 0 < r δ y ∧ r δ y < ρ :=
    ⟨shrinkingRadius_pos hR hδ.1 p t y,
      (hRadius δ hδ y (interior_subset hy)).trans_lt (half_lt_self hρ)⟩
  have hr : ContDiff ℝ ∞ (r δ) := contDiff_shrinkingRadius (contDiff_conformalDepth (normal := normal) 4) R p δ
  have hBall (y : X n) (hy : y ∈ Y) : closedBallImage (γ' lam) (E lam) (r δ) y ⊆ B :=
    closedBallImage_subset_of_normalCoordinates hNormalY hy (hRadius' y hy).1.le (hRadius' y hy).2.le
  have hBallEq (y : X n) (hy : y ∈ Y) :
      closedBallImage (γ' lam) (E lam) (r δ) y = closedBallImage (γ lam) (E lam) (r δ) y :=
    closedBallImage_congr_at (hγB (hYB hy)) _ _
  have hInnerSphere (y : X n) (hy : y ∈ Y) (w : ↥(standardSphere n)) :
      normalBallChartMap (E lam) (e' lam) y (r δ y) w ∈ B := by
    apply hBall y hy
    refine ⟨r δ y • frameVector (e' lam) y w, ?_, rfl⟩
    change metricPair (γ' lam) y (r δ y • frameVector (e' lam) y w)
      (r δ y • frameVector (e' lam) y w) ≤ (r δ y)^2
    rw [metricPair_smul_same, show metricPair (γ' lam) y (frameVector (e' lam) y w)
      (frameVector (e' lam) y w) = 1 from frameVector_mem_sphere (γ' lam) (e' lam) y (hFrame y hy) w,
      mul_one]
  have hO' : IsOpen O' := hO.inter (hBopen.prod hBopen)
  have hSameG : ProductSolutionOn (q₁' lam) (q₂' lam) O' G :=
    productSolution_congr_metrics hBopen hq₁B.symm hq₂B.symm inter_subset_right (hG.mono inter_subset_left)
  have hSphere (y : X n) (hy : y ∈ Y) (w : ↥(standardSphere n)) :
      (E lam (y,r δ y • frameVector (e' lam) y w),y) ∈ O' := by
    have hVel : (y,frameVector (e' lam) y w) ∈ bundle Y (γ' lam) :=
      ⟨hy,frameVector_mem_sphere (γ' lam) (e' lam) y (hFrame y hy) w⟩
    have hVel' : (y,frameVector (e' lam) y w) ∈ bundle Y (γ lam) := by
      rw [← bundle_congr (hγB.mono hYB)]
      exact hVel
    exact ⟨hCover _ hVel',hInnerSphere y hy w,hYB hy⟩
  have hSideFrame : ∀ y ∈ Y, y normal < -(1/4 : ℝ) → lam • y ∈ W' :=
    fun _ hy hl => hLowL hpL _ (ball_subset_closedBall (hYB hy)) hl.le
  have hNsub : normalPairDomain (interior Z) (γ' lam) ρ (E lam) ⊆ B ×ˢ interior Z :=
    normalPairDomain_subset_of_normalCoordinates interior_subset hNormalZ
  have hSameSeed : EqOn G (dilatedInitialGreen W' G₁ G₂ lam)
      (lowerNormalSeed normal (normalPairDomain (interior Z) (γ' lam) ρ (E lam))) := by
    intro z hz
    have hzN := hz.1.1
    have hzD := hB₃ (hZB (interior_subset (hNsub hzN).2))
    refine (hSeed (x := z) ?_).trans (dilatedInitialGreen_inter_eq G₁ G₂ z hzD).symm
    rw [← normalPairDomain_congr (hγB.mono (interior_subset.trans hZB))]
    exact hz
  obtain ⟨_,_,hΨ,hFlux,_⟩ := actualGreenTransfer hYopen hBopen hγs
    (smoothMetric_dilatedMetric hg₁' lam) (smoothMetric_dilatedMetric hg₂' lam)
    hE' hNormalY hsFrame hFrame hr hRadius' hO' hSameG hSphere
  have hΨ' : smoothNear (ψ lam δ) (bundle Y (γ lam)) := by
    rw [← bundle_congr (hγB.mono hYB)]
    exact hΨ
  have hDensityEq (u : X n → ℝ) (y : X n) (hy : y ∈ Y) :
      densityValue (E lam) (e' lam) (r δ) (ψ lam δ) u y =
        densityValue (E lam) (e lam) (r δ) (ψ lam δ) u y := by
    unfold densityValue
    congr 1
    funext w
    simp only [frameVector,heqFrame y (hYB hy)]
  have hFluxEq (u : X n → ℝ) (y : X n) (hy : y ∈ Y) :
      normalSphereGreenFlux (q₁' lam) (E lam) (e' lam) (r δ) G y u =
        normalSphereGreenFlux (q₁ lam) (E lam) (e lam) (r δ) G y u :=
    normalSphereGreenFlux_congr_at (heqFrame y (hYB hy)) (fun z hz => hq₁B (hInnerSphere y hy ⟨z,hz⟩))
  have hRep (u : X n → ℝ) (y : X n) (hy : y ∈ Y)
      (hu : HarmonicOnBall (q₁ lam) (closedBallImage (γ lam) (E lam) (r δ) y) u) :
      densityValue (E lam) (e lam) (r δ) (ψ lam δ) u y =
        normalSphereGreenFlux (q₁' lam) (E lam) (e' lam) (r δ) G y u := by
    rw [← hDensityEq u y hy]
    rw [← hBallEq y hy] at hu
    exact hFlux y hy u (harmonicOnBall_congr_metric (hq₁B.symm.mono (hBall y hy)) hu)
  refine ⟨O, ψ lam δ, hO, hG, hNseed, hSeed, hCover, hΨ', ?_, ?_, ?_, ?_⟩
  · intro y hy u hu
    exact (hRep u y hy hu).trans (hFluxEq u y hy)
  · intro y₀ hy₀ U hU u hu hU₀
    let U' := U ∩ B
    have hU' : IsOpen U' := hU.inter hBopen
    have hCover' : closedBallImage (γ' lam) (E lam) (r δ) y₀ ⊆ U' :=
      fun _ hx => ⟨hU₀ (hBallEq y₀ hy₀ ▸ hx),hBall y₀ hy₀ hx⟩
    have hUharm : Harmonic U' (q₁ lam) u := ⟨hu.1.mono inter_subset_left, fun _ hx => hu.2 _ hx.1⟩
    obtain ⟨V,hV,hyV,hVY,hCoverV,hH⟩ := exists_harmonic_normalSphereGreenFlux_near hYopen hγs
      (smoothMetric_dilatedMetric hg₁' lam) hE' hNormalY hO' hSameG hFrame
      (fun i => (hsFrame i).continuous.continuousOn) hr.continuous.continuousOn hRadius' hSphere
      hy₀ hU' hCover' (harmonic_congrOn hU' (hq₁B.symm.mono inter_subset_right) (fun _ _ => rfl) hUharm)
    have hCV (y : X n) (hy : y ∈ V) : closedBallImage (γ lam) (E lam) (r δ) y ⊆ U := by
      rw [← hBallEq y (hVY hy)]
      exact (hCoverV y hy).trans inter_subset_left
    refine ⟨V,hV,hyV,hVY,hCV,harmonic_congrOn hV (hq₂B.mono (hVY.trans hYB)) ?_ hH⟩
    intro y hy
    refine (hRep u y (hVY hy) ?_).symm
    refine ⟨⟨U,hU,hCV y hy,hu.1⟩,?_⟩
    exact fun x hx => hu.2 x (hCV y hy (interior_subset hx))
  · have hV (g : MetricField n) (u : X n → ℝ)
        (h : Harmonic {x | lam • x ∈ Ω} g u) : Harmonic DL g u :=
      ⟨h.1.mono (fun _ hx => hDΩ hx), fun _ hx => h.2 _ (hDΩ hx)⟩
    have hRepLocal (u v : X n → ℝ) (h₁ : Harmonic DL (q₁ lam) u)
        (h₂ : Harmonic DL (q₂ lam) v) (hEq : EqOn u v {y | lam • y ∈ W'}) (y : X n) (hy : y ∈ Y) :
        densityValue (E lam) (e lam) (r δ) (ψ lam δ) u y = v y := by
      have hCball : closedBallImage (γ lam) (E lam) (r δ) y ⊆ DL := by
        rw [← hBallEq y hy]
        exact (hBall y hy).trans hB₃
      have hOn : HarmonicOnBall (q₁ lam) (closedBallImage (γ lam) (E lam) (r δ) y) u :=
        ⟨⟨DL,hDL,hCball,h₁.1⟩, fun _ hx => h₁.2 _ (hCball (interior_subset hx))⟩
      exact (hRep u y hy hOn).trans (cylinderGreenFlux_reproduces hn hDopen hg₁' hg₂' hγs hG₁' hpL
        hB₃ hSideFrame hE' hNormalY hYZ hr.continuous.continuousOn hRadius' hFrame
        (fun i => (hsFrame i).continuous.continuousOn) hO' hSameG hSphere hSameSeed
        (harmonic_congrOn hDL hq₁DL.symm (fun _ _ => rfl) h₁)
        (harmonic_congrOn hDL hq₂DL.symm (fun _ _ => rfl) h₂) hEq hy)
    have hConst (g : MetricField n) : Harmonic DL g (fun _ => 1) := by
      have hCoord (i : I n) : coordDeriv i (fun _ => (1 : ℝ)) = fun _ => 0 := by
        funext x
        simp [coordDeriv]
      refine ⟨contDiff_const.contDiffOn, fun x _ => ?_⟩
      simp [laplace,hCoord,coordDeriv]
    intro y hy
    refine ⟨?_,?_,?_⟩
    · simpa only [densityValue,mul_one] using
        hRepLocal (fun _ => 1) (fun _ => 1) (hConst _) (hConst _) (fun _ _ => rfl) y hy
    · intro i
      exact hRepLocal _ _ (hV _ _ (harmonicCoordinates_dilated hΩ hg₁ hchart₁ lam i))
        (hV _ _ (harmonicCoordinates_dilated hΩ hg₂ hchart₂ lam i)) (fun _ _ => rfl) y hy
    · intro i
      exact hRepLocal _ _ (hV _ _ (harmonic_dilated hΩ hg₁ hchart₁ (hu₁ i) lam))
        (hV _ _ (harmonic_dilated hΩ hg₂ hchart₂ (hu₂ i) lam))
        (fun _ hx => hpair i hx.1) y hy
  · intro y hy hχ w
    obtain ⟨H,hH,hHeq⟩ := exists_framedGreenDensity_germ hΨ hsFrame hy (hFrame y hy)
      (w := w)
    refine ⟨H,hH,(hHeq.filter_mono nhdsWithin_le_nhds).trans ?_,?_⟩
    · have hLoc : ∀ᶠ z : X n × X n in 𝓝 (y,(w : X n)), z.1 ∈ B :=
        continuous_fst.continuousAt.preimage_mem_nhds (hBopen.mem_nhds (hYB hy))
      filter_upwards [hLoc.filter_mono nhdsWithin_le_nhds] with z hz
      change ψ lam δ (z.1, frameVector (e' lam) z.1 z.2) =
        ψ lam δ (z.1, frameVector (e lam) z.1 z.2)
      simp only [frameVector,heqFrame z.1 hz]
    · intro k
      rcases cylinderCutoff_differential_tsupport (normal := normal) htb hχ with hLower | hUpperY
      · let L := Y ∩ {z : X n | z normal < -(1/4 : ℝ)}
        have hL : IsOpen L := hYopen.inter
          (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous continuous_const)
        let K₁ := dilatedGreen G₁ lam
        have hqSmoothB : SmoothMetric B (q₁' lam) :=
          smoothMetric_restrict (smoothMetric_dilatedMetric hg₁' lam) (subset_univ B)
        have hGreen : GreenGerm B (q₁' lam) K₁ :=
          GreenGerm.restrict_congr_metric hDL hBopen hB₃
            (smoothMetric_restrict (smoothMetric_dilatedMetric hg₁' lam) (subset_univ DL))
            (fun _ _ => rfl)
            (GreenGerm.dilated (by omega : 2 ≤ n) hDopen
              (smoothMetric_restrict hg₁' (subset_univ D)) hG₁' hpL)
        have hyCap (z : X n) (hz : z ∈ Y) : r δ z ∈ Icc (0:ℝ) (ρ/2) :=
          ⟨(hRadius' z hz).1.le,hRadius δ hδ z (interior_subset hz)⟩
        have hEqLower (z : X n) (hz : z ∈ L) (u : ↥(standardSphere n)) :
            ψ lam δ (z,frameVector (e' lam) z u) = PL k ((lam,(z,r δ z)),u) := by
          let v : NormalGreenParameter n := (lam,(z,r δ z))
          have hv : v ∈ A.V := hJV ⟨hlam,interior_subset hz.1,hyCap z hz.1⟩
          have hKnown (x : X n)
              (hx : (x,z) ∈ normalPairDomain Y (γ' lam) ρ (E lam)) (hne : x ≠ z) :
              G (x,z) = K₁ (x,z) := by
            have hx' : (x,z) ∈ normalPairDomain (interior Z) (γ' lam) ρ (E lam) := by
              obtain ⟨ξ,hξ,hQ⟩ := hx
              exact ⟨ξ,⟨hYZ hξ.1,hξ.2⟩,hQ⟩
            exact (hSameSeed ⟨⟨hx',hz.2⟩,hne⟩).trans
              (dilatedInitialGreen_eq_left _ _ (hSideFrame z hz.1 hz.2))
          obtain ⟨U,hU,hUsub,hUψ⟩ := hΨ
          have hCψ : Continuous (fun u : ↥(standardSphere n) => ψ lam δ (z,frameVector (e' lam) z u)) :=
            hUψ.continuousOn.comp_continuous (continuous_const.prodMk
              ((continuous_frameVector (e' lam) z).comp continuous_subtype_val))
              (fun u => hUsub ⟨hz.1,frameVector_mem_sphere (γ' lam) (e' lam) z (hFrame z hz.1) u⟩)
          have hCPL : Continuous (fun u : ↥(standardSphere n) => PL k (v,u)) :=
            (hPL k).1.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
              (fun u => ⟨hv,show (u : X n) ≠ 0 from (norm_ne_zero_iff.mp
                ((mem_sphere_zero_iff_norm.mp u.property).trans_ne one_ne_zero))⟩)
          exact movingGreenFlux_eq_normalizedPoisson hYopen hBopen hγs
            (smoothMetric_dilatedMetric hg₁' lam) hE' hNormalY hO' hSameG hGreen hFrame
            (fun i => (hsFrame i).continuous.continuousOn) hr.continuous.continuousOn hRadius'
            hz.1 (hSphere z hz.1) hKnown hCψ (hFlux z hz.1) hWBall hBW (hAW v hv).1 A
            (hAW v hv).2 hCPL (hRepL k v hv) u
        have hLocalLow : (fun z : X n × X n => ψ lam δ (z.1,frameVector (e' lam) z.1 z.2))
            =ᶠ[𝓝 (y,(w : X n))] fun z => PL k ((lam,(z.1,r δ z.1)),z.2) := by
          have hLmem : ∀ᶠ z : X n × X n in 𝓝 (y,(w : X n)), z.1 ∈ L :=
            continuous_fst.continuousAt.preimage_mem_nhds
              (hL.mem_nhds (show y ∈ L from ⟨hy,hLower⟩))
          have hw₀ : (w : X n) ≠ 0 := by
            intro h0
            have hn := mem_sphere_zero_iff_norm.mp w.property
            simp [h0] at hn
          have hwmem : ∀ᶠ z : X n × X n in 𝓝 (y,(w : X n)), z.2 ≠ 0 :=
            continuous_snd.continuousAt.preimage_mem_nhds
              (isClosed_singleton.isOpen_compl.mem_nhds hw₀)
          filter_upwards [hLmem,hwmem] with z hz hz₀
          have hS := movingGreenFluxDensity_radial_frame (E := E lam) (r := r δ) (G := G)
            (g := q₁' lam) hz₀ (hFrame z.1 hz.1)
          exact (hS.trans (hEqLower z.1 hz ⟨sphereNormalize z.2,sphereNormalize_mem_sphere hz₀⟩)).trans
            ((hPL k).2 _ z.2 hz₀).symm
        have hEq := framedJet_eq_of_germ (hHeq.trans hLocalLow) k
        have hBnd := hJetL k lam hlam (r δ) hr y (interior_subset hy) (hyCap y hy)
          (hDjet δ hδ y (interior_subset hy)) w
        exact ⟨(le_of_eq (congrArg norm hEq.1)).trans (hBnd.1.trans (le_max_left _ _)),
          (le_of_eq (congrArg norm hEq.2)).trans (hBnd.2.trans (le_max_left _ _))⟩
      · let B₅ := ball (0 : X n) 5
        let O₀' := O₀ ∩ (B₅ ×ˢ B₅)
        have hO₀' : IsOpen O₀' := hO₀.inter (isOpen_ball.prod isOpen_ball)
        have hFroom' : fixedSeparationSet 4 (d/2) ⊆ O₀' := by
          intro z hz
          exact ⟨hFroom hz,mem_ball_zero_iff.mpr (hz.1.trans_lt (by norm_num)),
            mem_ball_zero_iff.mpr (hz.2.1.trans_lt (by norm_num))⟩
        have hq₁₅ : EqOn (q₁' lam) (q₁ lam) B₅ :=
          fun z hz => he₁ (hDil₅ lam hlam z (ball_subset_closedBall hz))
        have hq₂₅ : EqOn (q₂' lam) (q₂ lam) B₅ :=
          fun z hz => he₂ (hDil₅ lam hlam z (ball_subset_closedBall hz))
        have hF' : ProductSolutionOn (q₁' lam) (q₂' lam) O₀' F :=
          productSolution_congr_metrics isOpen_ball hq₁₅.symm hq₂₅.symm inter_subset_right
            (hF.mono inter_subset_left)
        have hTopAll (z : X n) (hz : z ∈ standardSphere n) :
            let q := normalGreenPoint E e' (lam,(y,r δ y)) z
            q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F := by
          have hv : (y,frameVector (e' lam) y z) ∈ bundle Y (γ' lam) :=
            ⟨hy,frameVector_mem_sphere (γ' lam) (e' lam) y (hFrame y hy) ⟨z,hz⟩⟩
          rw [bundle_congr (hγB.mono hYB)] at hv
          have hTopAt := hTop (y,frameVector (e' lam) y z) hv (show tb < t y from hUpperY)
          change (normalBallChartMap (E lam) (e' lam) y (r δ y) z,y) ∈ fixedSeparationSet 3 d ∧
            G =ᶠ[𝓝 (normalBallChartMap (E lam) (e' lam) y (r δ y) z,y)] F
          exact hTopAt
        have hRadCap (z : X n) (hz : z ∈ Y) : r δ z ∈ Ioc 0 (ρ/2) :=
          ⟨(hRadius' z hz).1,hRadius δ hδ z (interior_subset hz)⟩
        obtain ⟨T,hT,hTeq,hJets⟩ := hUpper k lam hlam (r δ) hr hRadCap hO₀' hFroom'
          F hF' hFB hO' G hSameG.1 (fun z hz w => hSphere z hz w) y hy
          (hDjet δ hδ y (interior_subset hy)) hTopAll w
        have hEq := framedJet_eq_of_germ (hHeq.trans hTeq.symm) k
        have hh := hJets k le_rfl
        exact ⟨(le_of_eq (congrArg norm hEq.1)).trans (hh.1.trans (le_max_right _ _)),
          (le_of_eq (congrArg norm hEq.2)).trans (hh.2.trans (le_max_right _ _))⟩

end CalderonPaper
