module

public import Proof.Manuscript.RadializedPhysicalMetric
public import Proof.Manuscript.PhysicalRadialAdjointZero
public import Proof.Manuscript.MovingTrace.RadializedCollar
public import Proof.Manuscript.MovingTrace.CompactNormalMetricFamily
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]

variable [Nontrivial (Fin dim)]

set_option maxHeartbeats 850000 in
/-- Exact physical reduction using the same radialized metric that the
signed-collar Poisson model uses, at the actual radius and actual slope. -/
theorem actualMovingTraceAdjoint_eq_radializedPhysical
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g q : ℝ → MetricField dim} {K : ℝ}
    {m : ℕ} {B : Fin (m+1) → ℝ} {e : ℝ → Frame dim} {E : ℝ → X dim × X dim → X dim}
    (lam : ℝ) (hB : Background Ω K B (γ lam) (g lam) (q lam) (e lam)) (hK : 0 < K)
    (hγ : SmoothMetric univ (γ lam)) (hg : SmoothMetric univ (g lam))
    (hE : ContDiff ℝ ∞ (E lam)) (he : ∀ i, ContDiff ℝ ∞ (fun y => e lam y i))
    {ρ : ℝ} (hN : NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    {r : X dim → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (i : I dim) {y : X dim} (hy : y ∈ Y) {c : ℝ} (hc : 0 < c)
    {U' : Set (X dim)} (hU' : IsOpen U') (hBU' : closedBall (0 : X dim) 1 ⊆ U')
    (hM : SmoothMetric U'
      (radializedMetric radialCutoff (fun x => symmetrizedNormalMetric g E e ((lam,y,r y),x))))
    {φ : X dim → ℂ} (hφ : smoothNear φ (standardSphere dim)) {z : X dim} (hz : z ∈ standardSphere dim) :
    let M := radializedMetric radialCutoff (fun x => symmetrizedNormalMetric g E e ((lam,y,r y),x))
    actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r i y
      (fun w => φ (movingBallToFrame (γ lam) (e lam) (y,w)).2) (frameVector (e lam) y z) =
      ((r y)⁻¹ : ℝ) • radialBallVelocityAdjoint M
        (fun x => scaledNormalTraceVelocity (γ lam) (E lam) (e lam) y (r y)
          (coordDeriv i r y) x (axis i)) (sphereGaussWeight M c) φ z := by
  dsimp only
  let M := radializedMetric radialCutoff (fun x => symmetrizedNormalMetric g E e ((lam,y,r y),x))
  let raw := normalizedBallMetric (g lam) (E lam) (e lam) y (r y)
  have hFrame (p : X dim) (hp : p ∈ Y) (j k : I dim) :
      metricPair (γ lam) p (e lam p j) (e lam p k) = if j=k then 1 else 0 :=
    hB.2.2.2.2.2.2.2 p (hN.center_mem hp) j k
  obtain ⟨U₀,hU₀,hBU₀,_,hReg,hPos,hVel⟩ := exists_smooth_movingBallFamilies
    (Y := Y) (Ω := Ω) (γ := γ lam) (g := g lam) (E := E lam) (e := e lam) (r := r)
    hγ hg hE hN he hFrame hr hR
  obtain ⟨D,hD,hSD,hφD⟩ := hφ
  let U : Set (X dim) := (Prod.mk y) ⁻¹' U₀
  have hU : IsOpen U := hU₀.preimage (continuous_const.prodMk continuous_id)
  have hBU : closedBall (0 : X dim) 1 ⊆ U := fun _ hx => hBU₀ ⟨hy,hx⟩
  have hRaw : SmoothMetric U raw := smoothMetric_movingBall_slice hReg hPos y
  let S : Set (X dim) := U ∩ (U' ∩ (D ∩ {0}ᶜ))
  have hS : IsOpen S := hU.inter (hU'.inter (hD.inter isClosed_singleton.isOpen_compl))
  have hSS : standardSphere dim ⊆ S := by
    intro x hx
    have hx' := sphere_subset_closedBall hx
    refine ⟨hBU hx',hBU' hx',hSD hx,?_⟩
    change x ≠ 0
    exact norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hx).trans_ne one_ne_zero)
  have hS₀ : (0 : X dim) ∉ S := fun hz => hz.2.2.2 rfl
  let L (x : X dim) : X dim × X dim := (y,x)
  have hL : ContDiff ℝ ∞ L := contDiff_const.prodMk contDiff_id
  have hLmap : MapsTo L S U₀ := fun _ hz => hz.1
  have hV' : ContDiffOn ℝ ∞ (movingBallScaledVelocity (γ lam) (E lam) (e lam) r i ∘ L) S :=
    (hVel i).comp hL.contDiffOn hLmap
  have hV : ContDiffOn ℝ ∞ (fun x => scaledNormalTraceVelocity (γ lam) (E lam) (e lam) y (r y)
      (coordDeriv i r y) x (axis i)) S := hV'
  have hs : r y ∈ Ico 0 ((fun _ : X dim => ρ) y) := ⟨(hR y hy).1.le,(hR y hy).2⟩
  have hEq : EqOn raw M (closedBall (0 : X dim) 1) :=
    normalizedBallMetric_eqOn_radialized_symmetrized hΩ lam hB hK hg hE hN hy hs
  have hWeight : EqOn (ballConormalVector raw)
      (fun x => (c * sphereGaussWeight M c x) • x) (standardSphere dim) := by
    intro x hx
    obtain ⟨a,ha,hGauss⟩ := normalizedBallMetric_radial_eigenline_on_closedBall
      hΩ hB hK hE hN hy hs (sphere_subset_closedBall hx)
    have hAt := ballConormalVector_eq_sphereGaussWeight_smul hc.ne' hx
      (hRaw.2 x (hBU (sphere_subset_closedBall hx))) ha.ne' hGauss
    have heq := ballConormalVector_congr_at (hEq (sphere_subset_closedBall hx))
    have hSc : sphereGaussWeight raw c x = sphereGaussWeight M c x := by
      change ⟪x,ballConormalVector raw x⟫_ℝ / c = ⟪x,ballConormalVector M x⟫_ℝ / c
      rw [heq]
    exact hAt.trans (congrArg (fun w : ℝ => (c*w) • x) hSc)
  exact actualMovingTraceAdjoint_eq_radialBallVelocityAdjoint i y (hFrame y hy)
    hU hS hU' hBU hBU' hSS (fun _ hx => hx.1) hS₀ hRaw hV
    ((sphereGaussWeight_contDiffOn hM c).mono (fun _ hx => hx.2.1))
    (fun x hx => (sphereGaussWeight_pos hc (hM.2 x hx.2.1) (fun e => hx.2.2.2 e)).ne')
    hc.ne' hWeight hM hEq (hφD.mono (fun _ hx => hx.2.2.1)) hz

end CalderonPaper
