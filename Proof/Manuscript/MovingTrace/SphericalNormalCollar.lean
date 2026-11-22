module

public import Proof.CalderonN.FramedNormalGauss
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open CalderonN Set Filter
open scoped InnerProductSpace ContDiff Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- In a chart of the unit sphere, positive collar height points into the
unit ball. -/
def polarCollar (sphereChart : A → X dim) (q : A × ℝ) : X dim :=
  (1 - q.2) • sphereChart q.1

omit [NeZero dim] in
theorem fderiv_polarCollar (sphereChart : A → X dim) (q z : A × ℝ)
    (hsphereChart : DifferentiableAt ℝ sphereChart q.1) :
    fderiv ℝ (polarCollar sphereChart) q z =
      (-z.2) • sphereChart q.1 + (1 - q.2) • fderiv ℝ sphereChart q.1 z.1 := by
  let ℓ := ContinuousLinearMap.snd ℝ A ℝ
  have hHeight : HasFDerivAt (fun x : A × ℝ => 1 - x.2) (-ℓ) q := by
    exact ℓ.hasFDerivAt.const_sub 1
  have hDirection := hsphereChart.hasFDerivAt.comp q (ContinuousLinearMap.fst ℝ A ℝ).hasFDerivAt
  have h := (hHeight.smul hDirection).fderiv
  change fderiv ℝ (polarCollar sphereChart) q = _ at h
  rw [h]
  simp [ℓ, add_comm]

theorem sphere_chart_fderiv_inner_eq_zero {Ω : Set A} (hΩ : IsOpen Ω)
    (sphereChart : A → X dim) (hsphereChart : ∀ x ∈ Ω, ‖sphereChart x‖ = 1)
    {x : A} (hx : x ∈ Ω) (hDiff : DifferentiableAt ℝ sphereChart x) (u : A) :
    ⟪sphereChart x, fderiv ℝ sphereChart x u⟫_ℝ = 0 := by
  have hConst : (fun p : A => ⟪sphereChart p, sphereChart p⟫_ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hΩ.mem_nhds hx] with p hp
    rw [real_inner_self_eq_norm_sq, hsphereChart p hp, one_pow]
  have h := fderiv_inner_apply (𝕜 := ℝ) hDiff hDiff u
  rw [hConst.fderiv_eq] at h
  have hZero : fderiv ℝ (fun _ : A => (1 : ℝ)) x u = 0 := by simp
  rw [hZero] at h
  have hComm : ⟪sphereChart x, fderiv ℝ sphereChart x u⟫_ℝ =
      ⟪fderiv ℝ sphereChart x u, sphereChart x⟫_ℝ := real_inner_comm _ _
  linarith only [h, hComm]

/-- The rescaled reference metric pulled back to a local spherical normal
collar has a unit radial coefficient and zero mixed principal coefficients.
This is the Gauss-lemma input for the boundary-layer transport system. -/
theorem framedNormalMetric_polarCollar_radial_block
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {γ : MetricField dim} (hEll : Elliptic Ω K γ) (hK : 0 < K)
    {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hNormal : NormalCoordinates Y Ω γ E R) {y : X dim} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame dim) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : r ≠ 0)
    {V : Set A} (hV : IsOpen V) (sphereChart : A → X dim)
    (hsphereChart : ∀ x ∈ V, ‖sphereChart x‖ = 1)
    (q : A × ℝ) (hq : q.1 ∈ V) (ht : q.2 < 1)
    (hDiff : DifferentiableAt ℝ sphereChart q.1)
    (hVelocity : r • frameVector e y (polarCollar sphereChart q) ∈ interior (disk γ y (R y))) :
    let g := framedNormalMetric γ e E y r
    let z := polarCollar sphereChart q
    let D := fderiv ℝ (polarCollar sphereChart) q
    metricPair g z (D (0,1)) (D (0,1)) = 1 ∧
      ∀ v : A, metricPair g z (D (0,1)) (D (v,0)) = 0 := by
  let g := framedNormalMetric γ e E y r
  let z := polarCollar sphereChart q
  let w := sphereChart q.1
  let σ := 1 - q.2
  have hσ : 0 < σ := sub_pos.mpr ht
  have hz : z = σ • w := rfl
  have hGauss (u : X dim) : metricPair g z z u = ⟪z,u⟫_ℝ := by
    rw [hNormal.framedNormalMetric_gauss hΩ hEll hK hy hyΩ e r hr z u hVelocity,
      metricPair_frameVector γ e y z u he, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  have hRad (u : X dim) : metricPair g z w u = ⟪w,u⟫_ℝ := by
    have h := hGauss u
    rw [hz, metricPair_smul_left, real_inner_smul_left] at h
    exact mul_left_cancel₀ hσ.ne' h
  have hUnit : metricPair g z w w = 1 := by
    rw [hRad, real_inner_self_eq_norm_sq, hsphereChart q.1 hq, one_pow]
  have hZero (v : A) : metricPair g z w (fderiv ℝ sphereChart q.1 v) = 0 :=
    (hRad _).trans (sphere_chart_fderiv_inner_eq_zero hV sphereChart hsphereChart hq hDiff v)
  dsimp only
  constructor
  · simp only [fderiv_polarCollar sphereChart q _ hDiff, map_zero, smul_zero, add_zero, neg_one_smul]
    change metricPair g z (-w) (-w) = _
    rw [← neg_one_smul ℝ w, metricPair_smul_left, metricPair_smul_right, hUnit]
    norm_num
  · intro v
    simp only [fderiv_polarCollar sphereChart q _ hDiff, map_zero, smul_zero, add_zero, neg_one_smul,
      neg_zero, zero_smul, zero_add]
    change metricPair g z (-w) (σ • fderiv ℝ sphereChart q.1 v) = _
    rw [← neg_one_smul ℝ w, metricPair_smul_left, metricPair_smul_right, hZero v]
    ring

end CalderonPaper
