module

public import Proof.CalderonN.ConformalActualGreenTransfer

import Proof.CalderonN.ConformalConstantTraceBound
import Proof.CalderonN.MovingTraceBackgroundBounds
import Proof.CalderonN.MetricCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Adapted from `ConformalGreenDensityJets` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 8500000

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}
open FixedTube MovingSphere

/-- Pointwise radius-weighted density and first trace estimates are
needed only where the cylinder cutoff varies. -/
@[expose] def UniformCylinderGreenDensityJets (normal : I dim)
    (g₁ g₂ : (MetricField dim)) (W Y' : Set (X dim)) (G₁ G₂ : (X dim) × (X dim) → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (ρ R ε tb : ℝ) : Prop :=
  let Y := interior (coordinateCylinder normal)
  let γ := conformalReference (depthScale normal 4) g₁
  let r := shrinkingRadius R p (conformalDepth normal 4)
  let χ := cylinderCutoff normal 4 tb
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
    ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) (dilatedMetric g₂ lam) (r δ) ε →
    ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ),
      let e (y : (X dim)) := smoothMetricFrame (γ lam y)
      let A := actualMovingTraceAdjoint (γ lam) (dilatedMetric g₁ lam) (E lam) e (r δ)
      let d := conformalSphereData normal g₁ g₂ E p R lam δ A
      let ψ := complexDensity (movingGreenFluxDensity (γ lam) (dilatedMetric g₁ lam) (E lam) e (r δ) G)
      IsOpen O ∧ ProductSolutionOn d.g₁ d.g₂ O G ∧
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        (endpoint d.expMap d.radius (y,frameVector d.frame y w),y) ∈ O) ∧
      EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' d.γ ρ d.expMap)) ∧
      ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere dim),
        let q := (y,frameVector d.frame y w)
        ‖(r δ y : ℂ) * (ψ-1) q‖ ≤ B ∧
        ∀ i, ‖(r δ y : ℂ) * traceDerivative d.γ A i (ψ-1) q‖ ≤ B

private theorem exists_uniform_cutoff_jet_bounds {Y : Set (X dim)} (hK : IsCompact Y)
    {χ : (X dim) → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ y ∈ Y,
      (∀ i, |coordDeriv i χ y| ≤ Q) ∧
      (∀ i j, |coordDeriv i (coordDeriv j χ) y| ≤ Q) := by
  have h₁ (i : (I dim)) : ContDiff ℝ ∞ (coordDeriv i χ) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h₂ (i j : (I dim)) : ContDiff ℝ ∞ (coordDeriv i (coordDeriv j χ)) :=
    ((h₁ j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let f (y : (X dim)) := ∑ i : (I dim), ∑ j : (I dim), (|coordDeriv i χ y| + |coordDeriv i (coordDeriv j χ) y|)
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((h₁ i).continuous.abs).add ((h₂ i j).continuous.abs)
  obtain ⟨Q,hQ⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 Q,le_max_left _ _,fun y hy => ?_⟩
  have h (i j : (I dim)) : |coordDeriv i χ y| + |coordDeriv i (coordDeriv j χ) y| ≤ max 0 Q := by
    have h₀ : ∀ i j, 0 ≤ |coordDeriv i χ y| + |coordDeriv i (coordDeriv j χ) y| :=
      fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    refine (Finset.single_le_sum (f := fun j => |coordDeriv i χ y| + |coordDeriv i (coordDeriv j χ) y|)
      (fun j _ => h₀ i j) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : (I dim),
        (|coordDeriv i χ y| + |coordDeriv i (coordDeriv j χ) y|))
      (fun i _ => Finset.sum_nonneg (fun j _ => h₀ i j)) (Finset.mem_univ i)).trans ?_
    exact (le_abs_self _).trans ((hQ y hy).trans (le_max_right _ _))
  exact ⟨fun i => (le_add_of_nonneg_right (abs_nonneg _)).trans (h i 0),
    fun i j => (le_add_of_nonneg_left (abs_nonneg _)).trans (h i j)⟩

/-- The uniform density jet estimate on the differential support, together
with the checked constant-mode cancellation, gives the protected output norm. -/
theorem uniformActualCylinderGreenTraceBound_of_densityJets
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {W Y' : Set (X dim)} {G₁ G₂ : (X dim) × (X dim) → ℝ} {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2)) (hY' : IsOpen Y')
    (hKY' : (coordinateCylinder normal) ⊆ Y')
    {p : ℕ} (hp : 1 ≤ p) {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Y' (ball (0 : (X dim)) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ interior (coordinateCylinder normal),
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2)
    (hJets : UniformCylinderGreenDensityJets normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb) :
    UniformActualCylinderGreenTraceBound normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb := by
  let S := Icc (-1 : ℝ) 1
  let K := (coordinateCylinder normal)
  let Y := interior K
  let γ := conformalReference (depthScale normal 4) g₁
  let k := dilatedMetric g₂
  let χ := cylinderCutoff normal 4 tb
  have hK : IsCompact K := isCompact_coordinateCylinder
  have hY : IsOpen Y := isOpen_interior
  have hχ : ContDiff ℝ ∞ χ := contDiff_cylinderCutoff (normal := normal) 4 tb
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have hγp (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef :=
    (hg₁.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)
  have hk (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => k q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₂.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hkp (lam : ℝ) (y : (X dim)) : (k lam y).PosDef := hg₂.2 _ (mem_univ _)
  obtain ⟨P,Γ,D,hP,hΓ,hD,hCoeff⟩ :=
    exists_uniform_movingTrace_coefficients (S := S) isCompact_Icc hK hγ hγp hk hkp
  obtain ⟨M₀,hM₀,hC⟩ := exists_uniform_conformal_movingTrace_one_bound (normal := normal) hg₁ hg₂ hE
    hK hY hY' interior_subset hKY' hp hρ hR hε hNormal hRadius
  obtain ⟨Q,hQ,hQjet⟩ := exists_uniform_cutoff_jet_bounds hK hχ
  obtain ⟨J,hJ,hJets⟩ := hJets
  have hv : Continuous (fun q : ℝ × (X dim) => chartVolume (γ q.1) q.2) :=
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j => (hγ i j).contDiffOn))).continuous.sqrt
  obtain ⟨V,hV⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK |>.exists_bound_of_continuousOn hv.continuousOn
  let V₀ := max 0 V
  let M₁ := (dim : ℝ)^2*P*(Q*J+2*Q*J+(dim : ℝ)*Γ*Q*J) + (dim : ℝ)*D*Q*J
  have hM₁ : 0 ≤ M₁ := by dsimp only [M₁]; positivity
  have hV₀ : 0 ≤ V₀ := le_max_left _ _
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨(M₀+M₁)*Real.sqrt ((volume : Measure (X dim)).real Y*V₀),by positivity,?_⟩
  filter_upwards [hS,hC,hJets] with lam hlam hc hj hpos δ hδ hSmall
  obtain ⟨O,G,hO,hG,hSphere,hLower,hpt⟩ := hj hpos δ hδ hSmall
  let g := dilatedMetric g₁ lam
  let e (y : (X dim)) := smoothMetricFrame (γ lam y)
  let r := shrinkingRadius R p (conformalDepth normal 4) δ
  let A := actualMovingTraceAdjoint (γ lam) g (E lam) e r
  let ψ := complexDensity (movingGreenFluxDensity (γ lam) g (E lam) e r G)
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  have hγ' : SmoothMetric univ (γ lam) :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun y _ => hγp lam y⟩
  have he (i : (I dim)) : ContDiff ℝ ∞ (fun y => e y i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame hγ'.1 hγ'.2 i)
  have hFrame (y : (X dim)) (_ : y ∈ Y) (i j : (I dim)) :
      metricPair (γ lam) y (e y i) (e y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγp lam y) i j
  have hE' : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius (contDiff_conformalDepth (normal := normal) 4) R p δ
  have hrp (y : (X dim)) (hy : y ∈ Y) : 0 < r y ∧ r y < ρ :=
    ⟨shrinkingRadius_pos hR hδ.1 p _ y,(hRadius δ hδ y hy).trans_lt (half_lt_self hρ)⟩
  obtain ⟨hDir,hAdj,hψ,_,hEq⟩ := actualGreenTransfer hY isOpen_ball hγ'
    (smoothMetric_dilatedMetric hg₁ lam) (smoothMetric_dilatedMetric hg₂ lam) hE'
    ((hNormal lam hlam).mono_centers (interior_subset.trans hKY')) he hFrame hr hrp hO hG hSphere
  have hψ' : smoothNear ψ (bundle Y (γ lam)) := by
    obtain ⟨U,hU,hBU,hs⟩ := hψ
    exact ⟨U,hU,hBU,Complex.ofRealCLM.contDiff.comp_contDiffOn hs⟩
  have hEq' : EqOn (movingTrace (γ lam) (k lam) r A ψ) 0 (bundle Y (γ lam)) :=
    eqOn_bundle_of_eqOn_frames hFrame (fun y hy w => hEq y hy w)
  have hv' : Continuous (chartVolume (γ lam)) := hv.comp (continuous_const.prodMk continuous_id)
  have hInt : IntegrableOn (chartVolume (γ lam)) Y :=
    (hv'.continuousOn.integrableOn_compact hK).mono_set interior_subset
  have hfin : (volume : Measure (X dim)) Y ≠ ⊤ :=
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
  have hmass : (∫ y in Y, chartVolume (γ lam) y) ≤ (volume : Measure (X dim)).real Y*V₀ := by
    have h := setIntegral_mono_on hInt (integrableOn_const (C := V₀) hfin) hY.measurableSet
      (fun y hy => (le_abs_self _).trans
        ((hV (lam,y) ⟨hlam,interior_subset hy⟩).trans (le_max_right _ _)))
    simpa only [setIntegral_const,smul_eq_mul] using h
  have hconst (y : (X dim)) (hy : y ∈ Y) (w : ↥(standardSphere dim)) :
      ‖baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (1 : (Field dim))) (y,frameVector d.frame y w)‖ ≤ M₀ := by
    have hχb : |χ y| ≤ 1 := by
      unfold χ cylinderCutoff
      rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))]
      exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul _)
    exact (norm_real_mul_le hχb (hc hpos δ hδ hSmall hDir hAdj y hy w)).trans_eq (one_mul _)
  have hcomm (y : (X dim)) (hy : y ∈ Y) (hχS : y ∈ tsupport (fderiv ℝ χ)) (w : ↥(standardSphere dim)) :
      ‖traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1) (y,frameVector d.frame y w)‖ ≤ M₁ := by
    obtain ⟨h₁,h₂⟩ := hQjet y (interior_subset hy)
    obtain ⟨hP',hΓ',hD'⟩ := hCoeff lam hlam y (interior_subset hy)
    obtain ⟨h₀,hW⟩ := hpt y hy hχS w
    exact norm_traceCutoffResidual_le d.γ d.g₂ d.radius d.adjoint χ (ψ-1)
      (y,frameVector d.frame y w) h₁ h₂ hΓ' hP' hD' h₀ hW
  use O,G,hO,hG,hSphere,hLower
  exact (traceNorm_cutoffDensity_le_of_bundle_bounds hY d hγ' hE' hr hDir hFrame hAdj hInt
    hχ hψ' hEq' hM₀ hM₁ hconst hcomm).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (add_nonneg hM₀ hM₁))

end CalderonN
