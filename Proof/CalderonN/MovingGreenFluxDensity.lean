module

public import Proof.CalderonN.MovingBallFamilies
public import Proof.CalderonN.NormalFluxDensity

import Mathlib.Tactic

/-! Adapted from `MovingGreenFluxDensity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Evaluate the conormal of boundary data itself, as opposed to the
conormal of its harmonic replacement. -/
@[expose] def rawParametricBallConormal
    (g : (X dim) × (X dim) → (Mat dim)) (b : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  ballConormal (fun z => g (q.1,z)) (fun z => b (q.1,z)) q.2

theorem contDiffOn_rawParametricBallConormal
    {S : Set ((X dim) × (X dim))} (hS : IsOpen S) {g : (X dim) × (X dim) → (Mat dim)} {b : (X dim) × (X dim) → ℝ}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) S)
    (hPos : ∀ q ∈ S, (g q).PosDef) (hb : ContDiffOn ℝ ∞ b S) :
    ContDiffOn ℝ ∞ (rawParametricBallConormal g b) S := by
  let C (q : (X dim) × (X dim)) := ballConormalVector (fun w => g (q.1,w)) q.2
  have hC : ContDiffOn ℝ ∞ C S := contDiffOn_product_ballConormalVector hg hPos
  have hD : ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => fderiv ℝ b q (0,C q)) S :=
    (hb.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_apply (contDiffOn_const.prodMk hC)
  apply hD.congr
  intro q hq
  have hSlice : HasFDerivAt (Prod.mk q.1) (ContinuousLinearMap.inr ℝ (X dim) (X dim)) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have h := (((hb.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp
    q.2 hSlice).fderiv
  rw [rawParametricBallConormal,ballConormal_eq_fderiv_conormalVector]
  change (fderiv ℝ (b ∘ Prod.mk q.1) q.2) (C q) = _
  rw [h]
  rfl

@[expose] def framedMovingGreenKernel
    (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ) (G : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  G (normalBallChartMap E e q.1 (r q.1) q.2,q.1)

/-- Surface density for the literal Green transfer, extended in the
angular variable along rays in the normal frame. -/
@[expose] def movingGreenFluxDensity
    (γ g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ)
    (G : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  let g' := movingBallMetric g E e r
  let b := framedMovingGreenKernel E e r G
  let p := movingBallToFrame γ e q
  (unitSphereArea dim) * ((r q.1)^(dim-2) *
    (parametricBallConormal g' b p - rawParametricBallConormal g' b (p.1,sphereNormalize p.2)))

set_option maxHeartbeats 1500000 in
theorem smoothNear_movingGreenFluxDensity
    {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {e : (Frame dim)} {r : (X dim) → ℝ}
    (hγ : SmoothMetric univ γ) (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hr : ContDiff ℝ ∞ r)
    {U T : Set ((X dim) × (X dim))} (hU : IsOpen U) (hT : IsOpen T)
    (hCU : Y ×ˢ closedBall (0 : (X dim)) 1 ⊆ U) (hST : Y ×ˢ (standardSphere dim) ⊆ T)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => movingBallMetric g E e r q i j) U)
    (hPos : ∀ q ∈ U, (movingBallMetric g E e r q).PosDef)
    {G : (X dim) × (X dim) → ℝ} (hG : ContDiffOn ℝ ∞ (framedMovingGreenKernel E e r G) T) :
    smoothNear (movingGreenFluxDensity γ g E e r G) (bundle Y γ) := by
  let m := movingBallMetric g E e r
  let b := framedMovingGreenKernel E e r G
  let P := movingBallToFrame γ e
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  let D (q : (X dim) × (X dim)) := (q.1,sphereNormalize q.2)
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hP : ContDiff ℝ ∞ P := contDiff_movingBallToFrame hγ he
  refine smoothNear_of_open_cover fun q hq => ?_
  have hAt : ∃ W, IsOpen W ∧ q ∈ W ∧ ContDiffOn ℝ ∞ (movingGreenFluxDensity γ g E e r G) W := by
    have hq' := movingBallToFrame_bundle hFrame hq
    have hn : (P q).2 ∈ N := by
      change (P q).2 ≠ 0
      intro hz
      have h := mem_sphere_zero_iff_norm.mp hq'.2
      change ‖(P q).2‖ = 1 at h
      simp [hz] at h
    obtain ⟨V,hV,hqV,hCon⟩ := exists_contDiffOn_parametricBallConormal hU hT q.1
      (fun _ hp => hCU ⟨mem_singleton_iff.mp hp.1 ▸ hq.1,hp.2⟩)
      (fun _ hp => hST ⟨mem_singleton_iff.mp hp.1 ▸ hq.1,hp.2⟩) hg hPos hG
    have hD : ContDiffOn ℝ ∞ D (V ×ˢ N) := contDiff_fst.contDiffOn.prodMk
      (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn (fun _ hp => hp.2))
    have hEq : D (P q) = P q := Prod.ext rfl (sphereNormalize_eq_of_sphere hq'.2)
    have hmem : D (P q) ∈ U ∩ T := by
      rw [hEq]
      exact ⟨hCU ⟨hq'.1,sphere_subset_closedBall hq'.2⟩,hST hq'⟩
    have hRaw := contDiffOn_rawParametricBallConormal (hU.inter hT)
      (fun i j => (hg i j).mono inter_subset_left) (fun p hp => hPos p hp.1) (hG.mono inter_subset_right)
    let W := (V ×ˢ N) ∩ D ⁻¹' (U ∩ T)
    have hW : IsOpen W := hD.continuousOn.isOpen_inter_preimage (hV.prod hN) (hU.inter hT)
    have hqW : P q ∈ W := ⟨⟨hqV,hn⟩,hmem⟩
    have hRawW := hRaw.comp (hD.mono (show W ⊆ V ×ˢ N from inter_subset_left))
      (show MapsTo D W (U ∩ T) from fun _ hp => hp.2)
    have hDiffW := (hCon.mono (show W ⊆ V ×ˢ N from inter_subset_left)).sub hRawW
    exact ⟨P ⁻¹' W,hW.preimage hP.continuous,hqW,
      contDiffOn_const.mul ((((hr.comp contDiff_fst).pow (dim-2)).contDiffOn).mul
        (hDiffW.comp hP.contDiffOn (fun _ hp => hp)))⟩
  exact hAt

set_option maxHeartbeats 1800000 in
/-- The smooth density is exactly the Green flux on the moving sphere. -/
theorem movingGreenFluxDensity_represents
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ)) {e : (Frame dim)} {r : (X dim) → ℝ} {y : (X dim)}
    (hy : y ∈ Y) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hr : 0 < r y) (hR : r y < ρ)
    {U : Set (X dim)} (hU : IsOpen U) (hCU : closedBall (0 : (X dim)) 1 ⊆ U)
    (hm : SmoothMetric U (fun z => movingBallMetric g E e r (y,z)))
    {G : (X dim) × (X dim) → ℝ}
    (hG : smoothNear (fun z => framedMovingGreenKernel E e r G (y,z)) (standardSphere dim))
    {u : (X dim) → ℝ} (hu : HarmonicOnBall g (closedBallImage γ E r y) u) :
    (∫ w : ↥(standardSphere dim), movingGreenFluxDensity γ g E e r G (y,frameVector e y w) *
      u (endpoint E r (y,frameVector e y w)) ∂(sphereProbability dim)) =
      normalSphereGreenFlux g E e r G y u := by
  let F := normalBallChartMap E e y (r y)
  let m (z : (X dim)) := movingBallMetric g E e r (y,z)
  let b (z : (X dim)) := framedMovingGreenKernel E e r G (y,z)
  let v := fixedBallPoisson m b
  have hV : FixedBallSolution m b v := fixedBallPoisson_solution hU hCU hm hG
  have hLap (z : (X dim)) (hz : z ∈ ball (0 : (X dim)) 1) :
      laplace (pullbackMetric g F) v z = 0 := by
    rw [laplace_pullback_normalizedBall hE hr hU (hCU (ball_subset_closedBall hz)) hm,
      hV.2.2 z hz,mul_zero]
  have h := normalSphereGreenFlux_eq_conormal_density hΩ hg hE hN hy he hr hR hu
    ⟨univ,isOpen_univ,subset_univ _,hV.1.contDiffOn⟩ hLap hG hV.2.1
  refine (integral_congr_ae (Filter.Eventually.of_forall (fun w : ↥(standardSphere dim) => ?_))).trans h.symm
  have hq := movingBallToFrame_fromFrame (γ := γ) (e := e) (w := (w : (X dim))) he
  change movingBallToFrame γ e (y,frameVector e y w) = (y,(w : (X dim))) at hq
  have hw := sphereNormalize_eq_of_sphere w.property
  have hdet : (m w).det ≠ 0 := (hm.2 w (hCU (sphere_subset_closedBall w.property))).det_pos.ne'
  have hPull : pullbackMetric g F = (r y)^2 • m := pullbackMetric_normalBallChartMap hE g e y (r y)
  change movingGreenFluxDensity γ g E e r G (y,frameVector e y w) * u (F w) =
    (unitSphereArea dim) * (ballConormal (pullbackMetric g F) v w -
      ballConormal (pullbackMetric g F) b w) * u (F w)
  rw [movingGreenFluxDensity,hq,parametricBallConormal,rawParametricBallConormal,hw,hPull]
  change (unitSphereArea dim) * ((r y)^(dim-2) * (ballConormal m v w - ballConormal m b w)) * u (F w) = _
  have hn : 2 ≤ dim := Fin.nontrivial_iff_two_le.mp (inferInstance : Nontrivial (Fin dim))
  rw [ballConormal_scaledMetric_sq hn m v w hdet hr,ballConormal_scaledMetric_sq hn m b w hdet hr]
  ring

end CalderonN
