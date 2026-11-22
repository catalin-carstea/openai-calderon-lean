module

public import Proof.CalderonN.NormalGreenCutoff
public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
public import Proof.CalderonN.BallGreenIdentity

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The transfer flux on the actual normal sphere, expressed in its
fixed unit-ball coordinates and in the pullback of the first metric. -/
@[expose] def normalSphereGreenFlux (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ)
    (G : (X dim) × (X dim) → ℝ) (y : (X dim)) (u : (X dim) → ℝ) : ℝ :=
  let F := normalBallChartMap E e y (r y)
  unitSphereFlux (wronskianFlux (pullbackMetric g F) (u ∘ F) fun z => G (F z,y))

set_option maxHeartbeats 1000000 in
/-- Compact cutoff evaluation and first-metric boundary flux agree on
the literal moving normal sphere. The Jacobian belongs to the exact
normal chart of that sphere. -/
theorem NormalGreenCutoff.pairing_eq_normalSphereGreenFlux
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g₁ g₂ : (MetricField dim)} (hg : SmoothMetric Ω g₁)
    {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {G : (X dim) × (X dim) → ℝ} (hG : ProductSolutionOn g₁ g₂ O G)
    {e : (Frame dim)} {r u φ : (X dim) → ℝ} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {η : ℝ} (h : NormalGreenCutoff Y γ ρ E V O r u y η φ) (hu : Harmonic Ω g₁ u) :
    greenCutoffPairing g₁ G φ y = normalSphereGreenFlux g₁ E e r G y u := by
  let F := normalBallChartMap E e y (r y)
  let D := ball (0 : (X dim)) (ρ/r y)
  let B := ball (0 : (X dim)) 1
  let k : (X dim) → ℝ := fun x => G (x,y)
  let S := D ∩ (fun x => (F x,y)) ⁻¹' O
  let g := pullbackMetric g₁ F
  have hr : 0 < r y := by linarith [h.width_pos,h.inner_pos]
  have hCap : r y < ρ := by linarith [h.width_pos,h.outer_lt]
  have hD : IsOpen D := isOpen_ball
  have hBD : closedBall (0 : (X dim)) 1 ⊆ D := closedBall_subset_ball ((lt_div_iff₀ hr).mpr (by simpa using hCap))
  have hFc : ContDiff ℝ ∞ F := contDiff_normalBallChartMap hE e y (r y)
  obtain ⟨hInj,hMap,hBij⟩ := normalBallChartMap_on_openBall hE hN hy he hr
  have hJ (x : (X dim)) (hx : x ∈ D) := coordinateJacobian_det_ne_zero (hBij x hx)
  have hgD : SmoothMetric D g := smoothMetric_pullbackMetric hg hFc hMap hJ
  have hImage : F '' B = normalBallRoom (normalPairDomain Y γ ρ E) γ V y (r y) :=
    normalBallChartMap_image_unitBall hExact hInv hy he hr hCap
  have hPhysicalSupport : tsupport φ ⊆ F '' B := by rw [hImage]; exact h.inside
  obtain ⟨χ,hχ,hχc,hχD,hχ1⟩ := Elliptic.exists_plateau_cutoff hD
    (isCompact_closedBall (0 : (X dim)) 1) hBD
  let φ' : (X dim) → ℝ := fun z => χ z * φ (F z)
  have hφ' : ContDiff ℝ ∞ φ' := hχ.mul (h.smooth.comp hFc)
  have hφ'c : HasCompactSupport φ' := hχc.mul_right
  have hφ'eq (z : (X dim)) (hz : z ∈ closedBall (0 : (X dim)) 1) : φ' =ᶠ[𝓝 z] φ ∘ F :=
    (hχ1 z hz).mono fun x hx => by simp [φ',hx]
  have hφ'B : tsupport φ' ⊆ B := by
    have hComp : tsupport (φ ∘ F) ⊆ F ⁻¹' tsupport φ :=
      closure_minimal (fun x hx => subset_tsupport φ hx)
        ((isClosed_tsupport φ).preimage hFc.continuous)
    intro z hz
    have hzD : z ∈ D := hχD (tsupport_mul_subset_left hz)
    obtain ⟨z',hz',hzz'⟩ := hPhysicalSupport (hComp (tsupport_mul_subset_right hz))
    exact (hInj (hBD (ball_subset_closedBall hz')) hzD hzz') ▸ hz'
  let a := (r y-η)/(r y)
  have ha : 0 < a := div_pos h.inner_pos hr
  have ha₁ : a < 1 := (div_lt_iff₀ hr).mpr (by linarith [h.width_pos])
  let P := interior {z : (X dim) | φ (F z) = u (F z)}
  have hPlateau : closedBall (0 : (X dim)) a ⊆ P := by
    intro z hz
    have hFz : F z ∈ closedBallImage γ E (fun _ => r y-η) y := by
      refine ⟨r y • frameVector e y z,?_,rfl⟩
      change metricPair γ y (r y • frameVector e y z) (r y • frameVector e y z) ≤ (r y-η)^2
      rw [metricPair_scaled_frameVector γ e y he]
      have hle := (le_div_iff₀ hr).mp (mem_closedBall_zero_iff.mp hz)
      have hsq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg z) hr.le) hle 2
      simpa only [mul_pow,mul_comm] using hsq
    exact mem_interior_iff_mem_nhds.mpr ((h.inner _ hFz).comp_tendsto hFc.continuous.continuousAt)
  obtain ⟨b,hb,hStep⟩ := (isCompact_closedBall (0 : (X dim)) a).exists_thickening_subset_open isOpen_interior hPlateau
  rw [thickening_closedBall hb ha.le] at hStep
  let a' := a + min (b/2) ((1-a)/2)
  have hmin : 0 < min (b/2) ((1-a)/2) := lt_min (by positivity) (by linarith)
  have ha' : a < a' := by dsimp [a']; linarith
  have ha'₁ : a' < 1 := by
    have ht := min_le_right (b/2) ((1-a)/2)
    dsimp [a']
    linarith
  have hap : a' ≤ b+a := by
    have ht := min_le_left (b/2) ((1-a)/2)
    dsimp [a']
    linarith
  have hpa : ball (0 : (X dim)) a' ⊆ P := (ball_subset_ball hap).trans hStep
  have hφ'a : EqOn φ' (u ∘ F) (ball (0 : (X dim)) a') := by
    intro z hz
    have hzP : z ∈ {x : (X dim) | φ (F x) = u (F x)} := interior_subset (hpa hz)
    exact (hφ'eq z (ball_subset_closedBall (ball_subset_ball ha'₁.le hz))).eq_of_nhds.trans hzP
  have hS : IsOpen S := hD.inter (hO.preimage (hFc.continuous.prodMk continuous_const))
  have hCollar : closedBall (0 : (X dim)) 1 \ ball (0 : (X dim)) a' ⊆ S := by
    intro z hz
    refine ⟨hBD hz.1,h.shell (F z) ?_⟩
    let v := r y • frameVector e y z
    have hHi : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
    have hLo : a' ≤ ‖z‖ := le_of_not_gt (fun hlt => hz.2 (mem_ball_zero_iff.mpr hlt))
    have hRad : metricPair γ y v v = (r y * ‖z‖)^2 := by
      rw [mul_pow]
      exact metricPair_scaled_frameVector γ e y he _ _
    have hNorm : r y * ‖z‖ ≤ r y := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hHi hr.le
    have hUp : r y * ‖z‖ < ρ := hNorm.trans_lt hCap
    have hVel : (y,v) ∈ normalVelocityDomain Y γ ρ :=
      ⟨hy,by rw [show metricPair γ y v v = _ from hRad]; exact pow_lt_pow_left₀ hUp (by positivity) (by decide)⟩
    refine ⟨⟨(y,v),hVel,rfl⟩,?_⟩
    have hRadial : normalRadialSq γ V (F z,y) = (r y * ‖z‖)^2 := by
      change metricPair γ y (V (E (y,v),y)) (V (E (y,v),y)) = _
      rw [hExact (y,v) hVel,hRad]
    rw [hRadial]
    have hLow : r y-η < r y * ‖z‖ := by
      have hlt := (div_lt_iff₀ hr).mp (ha'.trans_le hLo)
      linarith only [show r y-η < ‖z‖ * r y from hlt,
        show ‖z‖ * r y = r y * ‖z‖ from mul_comm _ _]
    refine ⟨pow_lt_pow_left₀ hLow h.inner_pos.le (by decide),?_⟩
    have hR : r y < r y+η := lt_add_of_pos_right _ h.width_pos
    exact pow_lt_pow_left₀ (hNorm.trans_lt hR) (mul_nonneg hr.le (norm_nonneg _)) (by decide : (2 : ℕ) ≠ 0)
  let Gslice := {x : (X dim) | (x,y) ∈ O}
  have hSlice : IsOpen Gslice := hO.preimage (continuous_id.prodMk continuous_const)
  have hk : Harmonic Gslice g₁ k :=
    (hG.mono (show Gslice ×ˢ ({y} : Set (X dim)) ⊆ O from fun (x,z) hz => by
      have hzy : z = y := mem_singleton_iff.mp hz.2
      subst z
      exact hz.1)).harmonic_left (mem_singleton y)
  have hk' : Harmonic S g (k ∘ F) := by
    refine ⟨hk.1.comp hFc.contDiffOn (fun _ hz => hz.2),fun z hz => ?_⟩
    exact (laplace_pullbackMetric (hΩ.inter hSlice)
      ⟨fun i j => (hg.1 i j).mono inter_subset_left,fun _ hx => hg.2 _ hx.1⟩
      hFc (hk.1.mono inter_subset_right) ⟨hMap hz.1,hz.2⟩ (hJ z hz.1)).trans (hk.2 _ hz.2)
  have hFlux := greenCutoffSource_eq_unitSphereFlux hD hS hBD ha'₁ hCollar hgD
    (hu.1.comp hFc.contDiffOn hMap) (fun z hz => by
      have hzD := hBD (ball_subset_closedBall hz)
      exact (laplace_pullbackMetric hΩ hg hFc hu.1 (hMap hzD) (hJ z hzD)).trans (hu.2 _ (hMap hzD)))
    hk' hφ' hφ'c hφ'B hφ'a
  change (∫ x, k x * greenCutoffSource g₁ φ x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := F '' B) (fun x hx =>
    mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun hz =>
      hx (hPhysicalSupport (tsupport_greenCutoffSource_subset g₁ φ hz)))))]
  rw [integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (X dim)) measurableSet_ball
    (fun z _ => (hFc.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt)
    (hInj.mono (ball_subset_closedBall.trans hBD))]
  suffices (∫ z in B, |LinearMap.det (fderiv ℝ F z).toLinearMap| •
      (k (F z) * greenCutoffSource g₁ φ (F z))) =
    ∫ z, (k ∘ F) z * greenCutoffSource g φ' z by exact this.trans hFlux
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun z hz =>
    mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun ht =>
      hz (hφ'B (tsupport_greenCutoffSource_subset g φ' ht)))))]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  have hzD := hBD (ball_subset_closedBall hz)
  obtain ⟨U,hU,hUo,hzU⟩ := _root_.mem_nhds_iff.mp
    (show {w : (X dim) | φ' w = (φ ∘ F) w} ∈ 𝓝 z from hφ'eq z (ball_subset_closedBall hz))
  have hL : laplace g φ' z = laplace g₁ φ (F z) :=
    (laplace_congrOn hUo (g := g) (h := g) (f := φ') (fun _ _ => rfl) (fun _ hw => hU hw) hzU).trans
    (laplace_pullbackMetric hΩ hg hFc h.smooth.contDiffOn (hMap hzD) (hJ z hzD))
  have hVol := chartVolume_pullbackMetric g₁ F z
  change chartVolume g z = _ at hVol
  simp only [Function.comp_apply,greenCutoffSource,hL,hVol,coordinateJacobian,coordinateMatrix_det_eq,smul_eq_mul]
  ring

end CalderonN
