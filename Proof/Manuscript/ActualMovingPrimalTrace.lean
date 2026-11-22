module

public import Proof.CalderonN.ActualGreenTransfer
import Proof.CalderonN.FixedBallPoissonCongruence
import Proof.CalderonN.CrossProductWeak
import Mathlib.Tactic

public section

noncomputable section
set_option maxHeartbeats 2600000

open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonPaper

open CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The physical primal trace uses the same scaled boundary velocity and
fixed normalized Dirichlet solve as the moving adjoint. -/
def actualMovingPrimalTrace (γ g : MetricField dim)
    (E : X dim × X dim → X dim) (e : Frame dim) (r : X dim → ℝ) : TraceAdjoint dim :=
  fun i y φ w =>
    let m := fun z => movingBallMetric g E e r (y,z)
    let V := movingBallScaledVelocity γ E e r i
    let p := movingBallToFrame γ e (y,w)
    let u := fixedBallPoisson m (fun z => (φ (frameVector e y z)).re)
    let v := fixedBallPoisson m (fun z => (φ (frameVector e y z)).im)
    ⟨(r y)⁻¹ * fderiv ℝ u p.2 (V p), (r y)⁻¹ * fderiv ℝ v p.2 (V p)⟩

theorem actualMovingPrimalTrace_eq_horizontal
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : MetricField dim}
    (hγ : SmoothMetric univ γ) (hg : SmoothMetric univ g)
    {ρ : ℝ} {E : X dim × X dim → X dim} (hE : ContDiff ℝ ∞ E)
    (hNormal : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : Frame dim} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {r : X dim → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ) :
    ∀ y ∈ Y, ∀ u, HarmonicOnBall g (closedBallImage γ E r y) u →
      ∀ i, ∀ w ∈ sphereAt γ y,
        let U := fun q => u (endpoint E r q)
        actualMovingPrimalTrace γ g E e r i y (fun v => (U (y,v) : ℂ)) w =
          ((show ℝ from horizontal γ U y w (axis i)) : ℂ) := by
  obtain ⟨U,hU,hCU,hDet,hm,hPos,hVel⟩ :=
    exists_smooth_movingBallFamilies hγ hg hE hNormal he hFrame hr hR
  intro y hy u hu i w hw
  let F := normalBallChartMap E e y (r y)
  let m := fun z => movingBallMetric g E e r (y,z)
  let V := movingBallScaledVelocity γ E e r i
  let D := fun v => u (endpoint E r (y,v))
  let w' := (movingBallToFrame γ e (y,w)).2
  have hw' : w' ∈ standardSphere dim := (movingBallToFrame_bundle hFrame ⟨hy,hw⟩).2
  have hMap : frameVector e y w' = w := by
    exact frameVector_frameCoordinates γ y w (e y) (hFrame y hy)
  have hW : w' ∈ closedBall (0 : X dim) 1 := sphere_subset_closedBall hw'
  let B : Set (X dim) := (Prod.mk y) ⁻¹' U
  have hB : IsOpen B := hU.preimage (continuous_const.prodMk continuous_id)
  have hCB : closedBall (0 : X dim) 1 ⊆ B := fun _ hz => hCU ⟨hy,hz⟩
  obtain ⟨S,hS,hCS,_,huS,hLap⟩ := harmonicOnBall_normalBallChartMap hΩ
    (smoothMetric_restrict hg (subset_univ Ω)) hE hNormal hy (hFrame y hy) (hR y hy).1 (hR y hy).2 hu
  let J := S ∩ B
  have hJ : IsOpen J := hS.inter hB
  have hCJ : closedBall (0 : X dim) 1 ⊆ J := fun _ hz => ⟨hCS hz,hCB hz⟩
  have hM : SmoothMetric J m :=
    smoothMetric_restrict (smoothMetric_movingBall_slice hm hPos y) inter_subset_right
  have huJ := huS.mono (show J ⊆ S from inter_subset_left)
  have hLapM (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : laplace m (u ∘ F) z = 0 := by
    have h := hLap z hz
    change laplace (pullbackMetric g F) (u ∘ F) z = 0 at h
    rw [laplace_pullback_normalizedBall hE (hR y hy).1 hJ (hCJ (ball_subset_closedBall hz)) hM] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (pow_ne_zero _ (hR y hy).1.ne'))
  obtain ⟨b,hb,_,Q,hQ,hCQ,hQJ,hbQ⟩ :=
    exists_contDiff_extension_near_compact hJ (isCompact_closedBall (0 : X dim) 1) hCJ huJ
  have hbSol : FixedBallSolution m (u ∘ F) b := by
    refine ⟨hb,fun z hz => hbQ (hCQ (sphere_subset_closedBall hz)),fun z hz => ?_⟩
    have hzQ := hCQ (ball_subset_closedBall hz)
    have hEq := laplace_congrOn (g := m) (h := m) hQ (fun _ _ => rfl)
      (show EqOn b (u ∘ F) Q from hbQ) hzQ
    exact hEq.trans (hLapM z hz)
  have hZero : FixedBallSolution m 0 0 := by
    refine ⟨contDiff_const,fun z _ => rfl,fun z _ => ?_⟩
    have hD (j : I dim) : coordDeriv j (0 : X dim → ℝ) = 0 := by
      funext x
      simp [coordDeriv]
    simp [laplace,hD]
  have hPoissonR : fderiv ℝ (fixedBallPoisson m (u ∘ F)) w' = fderiv ℝ b w' :=
    fixedBallPoisson_fderiv_eq_of_solution hJ hCJ hM hbSol (fun _ _ => rfl) hW
  have hPoissonI : fderiv ℝ (fixedBallPoisson m 0) w' = 0 :=
    (fixedBallPoisson_fderiv_eq_of_solution hJ hCJ hM hZero (fun _ _ => rfl) hW).trans (by simp)
  have hDeriv : fderiv ℝ b w' = fderiv ℝ (u ∘ F) w' :=
    (show b =ᶠ[𝓝 w'] u ∘ F from Filter.mem_of_superset (hQ.mem_nhds (hCQ hW)) hbQ).fderiv_eq
  have hHor : fderiv ℝ (u ∘ F) w' (V (y,w')) =
      r y * horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y w') (axis i) := by
    obtain ⟨Ju,hJu,hBu,huu⟩ := hu.1
    have hx : F w' ∈ closedBallImage γ E r y := by
      change F w' ∈ closedBallImage γ E (fun _ => r y) y
      rw [closedBallImage_eq_scaledFrameImage γ E e y (hFrame y hy) (hR y hy).1]
      exact mem_image_of_mem _ hW
    exact fderiv_scaledNormalTraceVelocity hE e (hr.differentiable (by simp) y)
      ((huu.contDiffAt (hJu.mem_nhds (hBu hx))).differentiableAt (by simp))
      (axis i) (hDet (y,w') (hCU ⟨hy,hW⟩))
  have hA : (fun z => ((D (frameVector e y z) : ℂ)).re) = u ∘ F := rfl
  have hB' : (fun z => ((D (frameVector e y z) : ℂ)).im) = 0 := rfl
  change (⟨(r y)⁻¹ * fderiv ℝ (fixedBallPoisson m _) w' (V (y,w')),
    (r y)⁻¹ * fderiv ℝ (fixedBallPoisson m _) w' (V (y,w'))⟩ : ℂ) = _
  rw [hA,hB',hPoissonR,hPoissonI,hDeriv,hHor,hMap]
  apply Complex.ext
  · change (r y)⁻¹ * (r y * _) = _
    rw [← mul_assoc,inv_mul_cancel₀ (hR y hy).1.ne',one_mul]
    rfl
  · simp

end CalderonPaper
