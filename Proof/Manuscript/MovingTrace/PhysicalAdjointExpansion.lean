module

public import Proof.Manuscript.MovingTrace.ActualRadialVelocityModel
public import Proof.Manuscript.ActualPhysicalRadializedAdjoint
public import Proof.Manuscript.PhysicalAdjointWeight
public import Proof.Manuscript.RadiusOperatorTaylor
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 5800000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "P" => MovingSymbolGeometry (n+1)

theorem radius_mul_coordDeriv_log_eq {r : Z → ℝ} (hr : ContDiff ℝ ∞ r)
    (i : I d) {y : Z} (hrp : 0 < r y) :
    r y * coordDeriv i (fun z => Real.log (r z)) y = coordDeriv i r y := by
  have h := (Real.hasDerivAt_log hrp.ne').comp_hasFDerivAt y
    (hr.differentiable (by simp) y).hasFDerivAt
  change r y * fderiv ℝ (Real.log ∘ r) y (axis i) = fderiv ℝ r y (axis i)
  rw [h.fderiv]
  change r y * ((r y)⁻¹ * fderiv ℝ r y (axis i)) = _
  rw [← mul_assoc,mul_inv_cancel₀ hrp.ne',one_mul]

/-- Convert the normalized signed-radius Taylor equality into the full
physical decomposition. The normal-model velocity is evaluated at the
same slope both at the actual radius and at zero. -/
theorem actualMovingTraceAdjoint_radius_expansion
    {Y Ω : Set Z} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g q : ℝ → MetricField d} {K : ℝ} {m : ℕ} {B : Fin (m+1) → ℝ}
    {e : ℝ → Frame d} {E : ℝ → Z × Z → Z}
    (lam : ℝ) (hB : Background Ω K B (γ lam) (g lam) (q lam) (e lam)) (hK : 0 < K)
    (hγ : SmoothMetric univ (γ lam)) (hg : SmoothMetric univ (g lam))
    (hE : ContDiff ℝ ∞ (E lam)) (he : ∀ j, ContDiff ℝ ∞ (fun y => e lam y j))
    {ρ : ℝ} (hN : NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    {r : Z → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (i : I d) {y : Z} (hy : y ∈ Y)
    {G : BallPoissonTube P d} (A : SmoothRadialVelocity G)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g E e (p.1.1,p.2)))
    (hW : ∀ p z, A.weight (p,z) = sphereGaussWeight (fun x => G.g (p,x)) 1 z)
    (hV : ∀ s z, A.velocity (((lam,y,s),coordDeriv i r y),z) =
      scaledNormalTraceVelocity (γ lam) (E lam) (e lam) y s (coordDeriv i r y) z (axis i))
    (hp : movingSymbolGeometryInput lam r i y ∈ A.U)
    (hp₀ : ((lam,y,0),coordDeriv i r y) ∈ A.U)
    {φ : Z → ℂ} (hφ : smoothNear φ S) {z : Z} (hz : z ∈ S) :
    let p := movingSymbolGeometryInput lam r i y
    let L := movingSymbolSignedRadiusEquiv d
    let a := (movingBallToFrame (γ lam) (e lam) (y,axis i)).2
    let fᵢ := coordDeriv i (fun w => Real.log (r w)) y
    actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r i y
      (fun w => φ (movingBallToFrame (γ lam) (e lam) (y,w)).2) (frameVector (e lam) y z) =
      ((r y)⁻¹ : ℂ) * flatAngularVelocityAdjoint (fun _ => a) φ z +
      (fᵢ : ℂ) * flatAngularVelocityAdjoint id φ z +
      (r y : ℂ) * radiusTaylorSphereOperator L A.operator p φ z +
      radiusFirstSphereOperator L A.operator p φ z := by
  let p := movingSymbolGeometryInput lam r i y
  let p₀ : P := ((lam,y,0),coordDeriv i r y)
  let L := movingSymbolSignedRadiusEquiv d
  let a := frameCoordinates (γ lam) y (e lam y) (axis i)
  let fᵢ := coordDeriv i (fun w => Real.log (r w)) y
  let M (p : P) : MetricField d := fun x => G.g (p,x)
  let O (p : P) : Set Z := (Prod.mk p) ⁻¹' G.U
  have hO (p : P) : IsOpen (O p) := G.openU.preimage (continuous_const.prodMk continuous_id)
  have hMetric {p : P} (hp : p ∈ A.U) : SmoothMetric (O p) (M p) := A.metric_smooth_at_p hp
  have hMw (p : P) : (fun x => A.weight (p,x)) = sphereGaussWeight (M p) 1 := funext (hW p)
  have hVp (s : ℝ) : (fun z => A.velocity (((lam,y,s),coordDeriv i r y),z)) =
      fun z => scaledNormalTraceVelocity (γ lam) (E lam) (e lam) y s (coordDeriv i r y) z (axis i) :=
    funext (hV s)
  have hMactual : M p = radializedMetric radialCutoff
      (fun x => symmetrizedNormalMetric g E e ((lam,y,r y),x)) := by
    funext x
    simp only [M,hG,radializedNormalFamily,p,movingSymbolGeometryInput]
  have hA := actualMovingTraceAdjoint_eq_radializedPhysical hΩ lam hB hK hγ hg hE he hN hr hR i hy
    (c := 1) one_pos (hO p) (A.closedBall_subset_metric_room hp)
    (by rw [← hMactual]; exact hMetric hp) hφ hz
  have hActual : actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r i y
      (fun w => φ (movingBallToFrame (γ lam) (e lam) (y,w)).2) (frameVector (e lam) y z) =
      (r y)⁻¹ • A.operator p φ z := by
    unfold SmoothRadialVelocity.operator
    change _ = (r y)⁻¹ • radialBallVelocityAdjoint (M p) _ _ φ z
    rw [hMw p,hMactual]
    change _ = (r y)⁻¹ • radialBallVelocityAdjoint _
      (fun z => A.velocity (((lam,y,r y),coordDeriv i r y),z)) _ φ z
    rw [hVp]
    exact hA
  obtain ⟨D,hD,hSD,hφD⟩ := hφ
  let D₀ := A.S ∩ D
  have hD₀ : IsOpen D₀ := A.openS.inter hD
  have hSD₀ : S ⊆ D₀ := subset_inter A.sphere_mem hSD
  have hD₀M : D₀ ⊆ O p₀ := fun x hx => A.tube_mem ⟨hp₀,hx.1⟩
  have hFrame (j k : I d) : metricPair (γ lam) y (e lam y j) (e lam y k) = if j=k then 1 else 0 :=
    hB.2.2.2.2.2.2.2 y (hN.center_mem hy) j k
  obtain ⟨c,hc,hConf⟩ := hB.2.2.2.1 y (hN.center_mem hy)
  have hMzero : M p₀ = radializedMetric radialCutoff
      (fun x => symmetrizedNormalMetric g E e ((lam,y,0),x)) := by
    funext x
    simp only [M,hG,radializedNormalFamily,p₀]
  have hEq : EqOn (normalizedBallMetric (g lam) (E lam) (e lam) y 0) (M p₀)
      (closedBall (0 : Z) 1) := by
    rw [hMzero]
    exact normalizedBallMetric_eqOn_radialized_symmetrized hΩ lam hB hK hg hE hN hy
      ⟨le_rfl,(hR y hy).1.trans (hR y hy).2⟩
  have hFlat : A.operator p₀ φ z = flatAngularVelocityAdjoint (fun _ => a) φ z +
      (r y*fᵢ) • flatAngularVelocityAdjoint id φ z := by
    unfold SmoothRadialVelocity.operator
    change radialBallVelocityAdjoint (M p₀) _ _ φ z = _
    rw [hMw p₀]
    change radialBallVelocityAdjoint (M p₀)
      (fun z => A.velocity (((lam,y,0),coordDeriv i r y),z)) _ φ z = _
    rw [hVp]
    have h := radialBallVelocityAdjoint_normalized_zero_weight_one hY hE hN hy hFrame hc hConf
      (coordDeriv i r y) i (hO p₀) hD₀ (A.closedBall_subset_metric_room hp₀) hSD₀ hD₀M
      (fun h => A.origin_off h.1) (hMetric hp₀) hEq (hφD.mono inter_subset_right) hz
    rw [h,flatAngularVelocityAdjoint_affine a (coordDeriv i r y) ⟨D,hD,hSD,hφD⟩ hz]
    rw [radius_mul_coordDeriv_log_eq hr i (hR y hy).1]
  have hT : A.operator p φ z = A.operator p₀ φ z +
      r y • radiusFirstSphereOperator L A.operator p φ z +
      r y ^ 2 • radiusTaylorSphereOperator L A.operator p φ z :=
    radiusSphereOperator_taylor_eq L A.operator p φ z (hR y hy).1.ne'
  simpa only [Complex.real_smul,Complex.ofReal_inv,movingBallToFrame,a] using
    inverse_radius_taylor_split (r y) fᵢ (hR y hy).1.ne' _ _ _ _ _ _ _ hActual hT hFlat

end CalderonPaper
