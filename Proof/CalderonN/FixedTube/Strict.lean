module

public import Proof.CalderonN.FixedTube.Phase
public import Proof.CalderonN.ProductMetricHessian

import Proof.CalderonN.MetricPair
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
The Euclidean scalar inequalities are adapted from
`Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
The bridge uses this project's protected metric and connection.
-/

@[expose] public section

noncomputable section
open Set Matrix
open scoped InnerProductSpace

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- the native normalization of `b1 = r ω` is `a1 = r⁻¹ ω`. -/
theorem tube_native_a1 {ω : (X dim)} {r : ℝ} (hr : r ≠ 0) (hω : ‖ω‖ = 1) :
    (⟪r • ω, r • ω⟫_ℝ)⁻¹ • (r • ω) = r⁻¹ • ω := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hω, smul_smul]
  congr 1
  first | (field_simp; done) | (field_simp; ring)

/-- the native normalization of `b2 = -(r q)` is `a2 = -((r ‖q‖²)⁻¹) q`. -/
theorem tube_native_a2 {q : (X dim)} {r : ℝ} (hr : r ≠ 0) (hq : q ≠ 0) :
    (⟪-(r • q), -(r • q)⟫_ℝ)⁻¹ • (-(r • q)) = -((r * ‖q‖ ^ 2)⁻¹) • q := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [inner_neg_left, inner_neg_right, neg_neg, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, smul_neg, smul_smul, neg_smul]
  congr 2
  first | (field_simp; done) | (field_simp; ring)

/-- the literal identity-metric constraints on `v1` give `‖r v1‖ = 1` and `r v1 ⊥ ω`. -/
theorem tube_native_v1_constraints {ω v : (X dim)} {r : ℝ} (hr : r ≠ 0) (hω : ‖ω‖ = 1)
    (h1 : ⟪v, r⁻¹ • ω⟫_ℝ = 0) (h2 : ⟪v, v⟫_ℝ = ⟪r⁻¹ • ω, r⁻¹ • ω⟫_ℝ) :
    ‖r • v‖ = 1 ∧ ⟪r • v, ω⟫_ℝ = 0 := by
  rw [real_inner_smul_right] at h1
  have h1' : ⟪v, ω⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (inv_ne_zero hr)
    · exact h
  refine ⟨?_, by rw [real_inner_smul_left, h1', mul_zero]⟩
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, hω, mul_one,
    norm_inv] at h2
  have hr' : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hsq : ‖r • v‖ ^ 2 = 1 := by
    rw [norm_smul, mul_pow, h2]
    first | (field_simp; done) | (field_simp; ring)
  have hnn : 0 ≤ ‖r • v‖ := norm_nonneg _
  nlinarith [hsq, hnn]

/-- the literal identity-metric constraints on `v2` give `r v2 ⊥ q` and `‖r v2‖ ‖q‖ = 1`. -/
theorem tube_native_v2_constraints {q v : (X dim)} {r : ℝ} (hr : r ≠ 0) (hq : q ≠ 0)
    (h1 : ⟪v, -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ = 0)
    (h2 : ⟪v, v⟫_ℝ = ⟪-((r * ‖q‖ ^ 2)⁻¹) • q, -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ) :
    ⟪r • v, q⟫_ℝ = 0 ∧ ‖r • v‖ * ‖q‖ = 1 := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hc : -((r * ‖q‖ ^ 2)⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero hr (pow_ne_zero 2 hn)))
  rw [real_inner_smul_right] at h1
  have h1' : ⟪v, q⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · exact h
  refine ⟨by rw [real_inner_smul_left, h1', mul_zero], ?_⟩
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, mul_pow, norm_neg,
    norm_inv, norm_mul, norm_pow, norm_norm] at h2
  have hr' : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hsq : (‖r • v‖ * ‖q‖) ^ 2 = 1 := by
    rw [norm_smul, mul_pow, mul_pow, h2]
    first | (field_simp; done) | (field_simp; ring)
  have hnn : 0 ≤ ‖r • v‖ * ‖q‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hsq, hnn]


private theorem metricPair_identity (x u v : (X dim)) :
    metricPair (fun _ => (1 : (Mat dim))) x u v = ⟪u,v⟫_ℝ := by
  rw [metricPair_eq_dotProduct]
  simp only [Matrix.one_mulVec, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

private theorem connection_identity (x v w : (X dim)) :
    connection (fun _ => (1 : (Mat dim))) x v w = 0 := by
  ext k
  simp [connection, christoffel, coordDeriv]

private theorem axis_covector_riesz {f : (X dim) → ℝ} {x B : (X dim)}
    (h : ∀ i, coordDeriv i f x = ⟪B,axis i⟫_ℝ) :
    (fun i => coordDeriv i f x) = fun i => B i := by
  funext i
  rw [h, axis]
  simp [EuclideanSpace.inner_single_right]

private theorem identity_gradient_riesz {f : (X dim) → ℝ} {x B : (X dim)}
    (h : (fun i => coordDeriv i f x) = fun i => B i) :
    chartMetricGradient (fun _ => (1 : (Mat dim))) f x = B := by
  ext i
  change (((1 : (Mat dim))⁻¹) *ᵥ (fun i => coordDeriv i f x)) i = B i
  rw [inv_one, Matrix.one_mulVec]
  exact congrFun h i

private theorem coords_ne_zero {B : (X dim)} (h : B ≠ 0) : (fun i => B i) ≠ 0 := by
  intro he
  apply h
  ext i
  exact congrFun he i

/-- The Euclidean scalar estimate implies strictness for the literal product Hessian. -/
theorem tube_native_strict_of_form (M e0 a σ : ℝ) {Y ω q : (X dim)} {r k s : ℝ}
    (ht : 0 < tubeHeight normal M e0 Y) (hω : ‖ω‖ = 1)
    (hrd : tubeRadius normal M e0 a σ Y = r) (hkd : a * (1 + σ) * tubeHeight normal M e0 Y ^ σ = k)
    (hsd : a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) = s)
    (hqd : ω + k • tubeHeightGrad normal e0 Y = q) (hr : r ≠ 0) (hq : q ≠ 0)
    (hE : ∀ v1 v2 : (X dim), ‖r • v1‖ = 1 → ⟪r • v1, ω⟫_ℝ = 0 → ⟪r • v2, q⟫_ℝ = 0 →
      ‖r • v2‖ * ‖q‖ = 1 →
      0 < ⟪r⁻¹ • ω + -((r * ‖q‖ ^ 2)⁻¹) • q, r⁻¹ • ω + -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ +
        ⟪v1 - v2, v1 - v2⟫_ℝ - (k * tubeHeightDeriv normal e0 Y (-((r * ‖q‖ ^ 2)⁻¹) • q)) ^ 2 -
        (k * tubeHeightDeriv normal e0 Y v2) ^ 2 -
        r * (s * tubeHeightDeriv normal e0 Y (-((r * ‖q‖ ^ 2)⁻¹) • q) ^ 2 +
          k * (2 * e0 * transversePair normal (-((r * ‖q‖ ^ 2)⁻¹) • q) (-((r * ‖q‖ ^ 2)⁻¹) • q)) +
          s * tubeHeightDeriv normal e0 Y v2 ^ 2 + k * (2 * e0 * transversePair normal v2 v2))) :
    ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
      (tubePhase normal M e0 a σ) (Y + r • ω,Y) := by
  subst hrd hkd hsd hqd
  let r := tubeRadius normal M e0 a σ Y
  let q := ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y
  let p : (X dim) × (X dim) := (Y + r • ω,Y)
  let f₁ (x : (X dim)) := tubePhase normal M e0 a σ (x,Y)
  let f₂ (y : (X dim)) := tubePhase normal M e0 a σ (p.1,y)
  have hd : DifferentiableAt ℝ (tubePhase normal M e0 a σ) p :=
    (tube_phase_fderiv_apply (normal := normal) M e0 a σ ht).1
  have hc₁ : (fun i => coordDeriv i f₁ p.1) = fun i => (r • ω : (X dim)) i :=
    axis_covector_riesz fun i => by
      rw [(slice_coordDeriv _ p hd i).1, (tube_phase_partial_jets (normal := normal) M e0 a σ ht (axis i) 0).1,
        real_inner_smul_left]
  have hc₂ : (fun i => coordDeriv i f₂ p.2) = fun i => (-(r • q) : (X dim)) i :=
    axis_covector_riesz fun i => by
      rw [(slice_coordDeriv _ p hd i).2, (tube_phase_partial_jets (normal := normal) M e0 a σ ht 0 (axis i)).2,
        inner_neg_left, real_inner_smul_left]
  have h₁ := identity_gradient_riesz hc₁
  have h₂ := identity_gradient_riesz hc₂
  let g : (MetricField dim) := fun _ => 1
  let a₁ : (X dim) := (covectorSq g f₁ p.1)⁻¹ • chartMetricGradient g f₁ p.1
  let a₂ : (X dim) := (covectorSq g f₂ p.2)⁻¹ • chartMetricGradient g f₂ p.2
  have ha₁ : a₁ = r⁻¹ • ω := by
    dsimp only [a₁]
    rw [← metricPair_gradient_self g f₁ p.1 Matrix.PosDef.one,
      h₁, metricPair_identity]
    exact tube_native_a1 hr hω
  have ha₂ : a₂ = -((r * ‖q‖ ^ 2)⁻¹) • q := by
    dsimp only [a₂]
    rw [← metricPair_gradient_self g f₂ p.2 Matrix.PosDef.one,
      h₂, metricPair_identity]
    exact tube_native_a2 hr hq
  obtain ⟨D,hD,hDe⟩ := tube_phase_second_jet (normal := normal) M e0 a σ (x := p.1) ht
  have hH (v w : (X dim) × (X dim)) : productMetricHessian g g (tubePhase normal M e0 a σ) p v w = D v w := by
    rw [productMetricHessian, connection_identity, connection_identity, hD.fderiv,
      Prod.mk_zero_zero, map_zero, sub_zero]
  have hωne : ω ≠ 0 := by
    intro h
    simp [h] at hω
  change (fun i => coordDeriv i f₁ p.1) ≠ 0 ∧
    (fun i => coordDeriv i f₂ p.2) ≠ 0 ∧ ∀ v w : (X dim),
      metricPair g p.1 (chartMetricGradient g f₁ p.1) v = 0 →
      metricPair g p.1 v v = metricPair g p.1 a₁ a₁ →
      metricPair g p.2 (chartMetricGradient g f₂ p.2) w = 0 →
      metricPair g p.2 w w = metricPair g p.2 a₂ a₂ →
      0 < productMetricHessian g g (tubePhase normal M e0 a σ) p (a₁,-a₂) (a₁,-a₂) +
        productMetricHessian g g (tubePhase normal M e0 a σ) p (v,w) (v,w)
  refine ⟨hc₁ ▸ coords_ne_zero (smul_ne_zero hr hωne),
    hc₂ ▸ coords_ne_zero (neg_ne_zero.mpr (smul_ne_zero hr hq)), ?_⟩
  intro v w hv hvn hw hwn
  rw [h₁, metricPair_identity, real_inner_smul_left] at hv
  rw [h₂, metricPair_identity, inner_neg_left, real_inner_smul_left] at hw
  rw [metricPair_identity, metricPair_identity, ha₁] at hvn
  rw [metricPair_identity, metricPair_identity, ha₂] at hwn
  have hvω : ⟪v,r⁻¹ • ω⟫_ℝ = 0 := by
    rw [inner_smul_right, real_inner_comm ω v, (mul_eq_zero.mp hv).resolve_left hr, mul_zero]
  have hwq : ⟪w,-((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ = 0 := by
    rw [inner_smul_right, real_inner_comm q w,
      (mul_eq_zero.mp (neg_eq_zero.mp hw)).resolve_left hr, mul_zero]
  obtain ⟨hvnorm,hvorth⟩ := tube_native_v1_constraints hr hω hvω hvn
  obtain ⟨hworth,hwnorm⟩ := tube_native_v2_constraints hr hq hwq hwn
  rw [hH, hH, ha₁, ha₂, tube_phase_hessian_sum (normal := normal) hDe]
  exact hE v w hvnorm hvorth hworth hwnorm

/-- the N6 scalar at `V1 = r⁻¹ v`, `V2 = r⁻¹ w` is `r⁻²` times T12's flat form `E` minus the two actual
`r D²r` corrections at `u = ‖ω+b‖⁻² (ω+b)` and `w`. -/
theorem tube_native_scalar_scale {ω b v w : (X dim)} {r k s e0 : ℝ} (d : (X dim) →L[ℝ] ℝ) (hr : r ≠ 0)
    (hd : ∀ U : (X dim), k * d U = ⟪b, U⟫_ℝ) :
    ⟪r⁻¹ • ω + -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b), r⁻¹ • ω + -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)⟫_ℝ +
        ⟪r⁻¹ • v - r⁻¹ • w, r⁻¹ • v - r⁻¹ • w⟫_ℝ -
        (k * d (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b))) ^ 2 - (k * d (r⁻¹ • w)) ^ 2 -
        r * (s * d (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)) ^ 2 +
          k * (2 * e0 * transversePair normal (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)) (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b))) +
          s * d (r⁻¹ • w) ^ 2 + k * (2 * e0 * transversePair normal (r⁻¹ • w) (r⁻¹ • w))) =
      (r ^ 2)⁻¹ * ((‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
          ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2) -
        r * (s * d ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) ^ 2 +
          k * (2 * e0 * transversePair normal ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) ((‖ω + b‖ ^ 2)⁻¹ • (ω + b))) +
          s * d w ^ 2 + k * (2 * e0 * transversePair normal w w))) := by
  have hQ : -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b) = -(r⁻¹ • ((‖ω + b‖ ^ 2)⁻¹ • (ω + b))) := by
    rw [smul_smul, mul_inv, neg_smul]
  generalize (‖ω + b‖ ^ 2)⁻¹ • (ω + b) = u at hQ ⊢
  have hP : r⁻¹ • ω + -(r⁻¹ • u) = r⁻¹ • (ω - u) := by rw [smul_sub, sub_eq_add_neg]
  rw [hQ, hP, ← smul_sub r⁻¹ v w]
  simp only [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← hd u, ← hd w]
  simp only [map_neg, map_smul, smul_eq_mul, transversePair_neg_same, transversePair_smul_same]
  field_simp

/-- with `m0` chosen from T12 by `amin, Bb, ε` BEFORE `σ, e0, T0` and the tube data, the literal native
identity-metric `ProductHessianStrictAt` holds for the SAME `tubePhase` whenever the actual `r D²r`
corrections stay below `m0`. -/
theorem tube_native_strict_of_margin {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ (M e0 a σ : ℝ) (Y ω : (X dim)), 0 < tubeHeight normal M e0 Y →
      0 < tubeRadius normal M e0 a σ Y → ‖ω‖ = 1 →
      amin ≤ ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ →
      ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ≤ Bb →
      ε ≤ ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ →
      ε ≤ ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y + (2 : ℝ) • ω‖ →
      (∀ w : (X dim), ⟪w, ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y⟫_ℝ = 0 →
        ‖w‖ * ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ = 1 →
        tubeRadius normal M e0 a σ Y *
          (a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) * tubeHeightDeriv normal e0 Y
            ((‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y)) ^ 2 +
          a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * (2 * e0 *
            transversePair normal ((‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y)) ((‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y))) +
          a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) * tubeHeightDeriv normal e0 Y w ^ 2 +
          a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * (2 * e0 * transversePair normal w w)) < m0) →
      ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
        (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω,Y) := by
  obtain ⟨m0, hm0, hT12⟩ := tube_flat_form_compact_min (Bb := Bb) ham hε
  refine ⟨m0, hm0, fun M e0 a σ Y ω ht hr hω hb1 hb2 hn1 hn2 hcorr => ?_⟩
  have hq : ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y ≠ 0 := fun h => by
    rw [h, norm_zero] at hn1
    linarith
  refine tube_native_strict_of_form M e0 a σ ht hω rfl rfl rfl rfl hr.ne' hq
    (fun v1 v2 hv1 hv1ω hv2q hv2 => ?_)
  have hd : ∀ U : (X dim), a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * tubeHeightDeriv normal e0 Y U =
      ⟪(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y, U⟫_ℝ := fun U => by
    rw [tubeHeightDeriv_eq_inner, real_inner_smul_left]
  have e1 : v1 = (tubeRadius normal M e0 a σ Y)⁻¹ • (tubeRadius normal M e0 a σ Y • v1) :=
    (inv_smul_smul₀ hr.ne' v1).symm
  have e2 : v2 = (tubeRadius normal M e0 a σ Y)⁻¹ • (tubeRadius normal M e0 a σ Y • v2) :=
    (inv_smul_smul₀ hr.ne' v2).symm
  have hscale := tube_native_scalar_scale (normal := normal) (ω := ω) (v := tubeRadius normal M e0 a σ Y • v1)
    (w := tubeRadius normal M e0 a σ Y • v2) (s := a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1))
    (e0 := e0) (tubeHeightDeriv normal e0 Y) hr.ne' hd
  rw [← e1, ← e2] at hscale
  rw [hscale]
  have hE := hT12 ω (tubeRadius normal M e0 a σ Y • v1)
    ((a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y) (tubeRadius normal M e0 a σ Y • v2)
    hω hv1ω hv1 hv2q hv2 hb1 hb2 hn1 hn2
  have hC := hcorr (tubeRadius normal M e0 a σ Y • v2) hv2q hv2
  have hr2 : 0 < (tubeRadius normal M e0 a σ Y ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  exact mul_pos hr2 (by linarith)

/-- one actual `r D²r` correction term is at most `σ Bb² L² + 4 e0 Bb R L²`. -/
theorem tube_corr_term_le {r s k e0 σ D transverseSq nb nx Bb R L : ℝ}
    (hrs : r * s = σ / (1 + σ) * k ^ 2) (hσ : 0 ≤ σ) (he0 : 0 ≤ e0) (hk0 : 0 ≤ k) (hkB : k ≤ Bb)
    (hr0 : 0 ≤ r) (hrR : r ≤ R) (hD : |k * D| ≤ nb * nx) (hnb : 0 ≤ nb) (hnbB : nb ≤ Bb)
    (hnx : 0 ≤ nx) (hnxL : nx ≤ L) (hX0 : 0 ≤ transverseSq) (hX : transverseSq ≤ 2 * nx ^ 2) :
    r * (s * D ^ 2 + k * (2 * e0 * transverseSq)) ≤
      σ * Bb ^ 2 * L ^ 2 + 4 * e0 * Bb * R * L ^ 2 := by
  have hB0 : 0 ≤ Bb := hnb.trans hnbB
  have hL0 : 0 ≤ L := hnx.trans hnxL
  have h1 : r * (s * D ^ 2) = σ / (1 + σ) * (k * D) ^ 2 := by
    rw [← mul_assoc, hrs]
    ring
  have hkd : |k * D| ≤ Bb * L := hD.trans (mul_le_mul hnbB hnxL hnx hB0)
  have h2 : (k * D) ^ 2 ≤ (Bb * L) ^ 2 := sq_le_sq' (abs_le.mp hkd).1 (abs_le.mp hkd).2
  have h3 : σ / (1 + σ) ≤ σ := div_le_self hσ (by linarith)
  have h5 : σ / (1 + σ) * (k * D) ^ 2 ≤ σ * (Bb * L) ^ 2 := mul_le_mul h3 h2 (sq_nonneg _) hσ
  have hnx2 : nx ^ 2 ≤ L ^ 2 := by nlinarith
  have h6 : transverseSq ≤ 2 * L ^ 2 := hX.trans (by linarith)
  have h7 : r * (k * (2 * e0 * transverseSq)) ≤ R * (Bb * (2 * e0 * (2 * L ^ 2))) :=
    mul_le_mul hrR (mul_le_mul hkB (mul_le_mul_of_nonneg_left h6 (by positivity))
      (by positivity) hB0) (by positivity) (hr0.trans hrR)
  have h8 : r * (s * D ^ 2 + k * (2 * e0 * transverseSq)) =
      r * (s * D ^ 2) + r * (k * (2 * e0 * transverseSq)) := mul_add _ _ _
  have h9 : σ * (Bb * L) ^ 2 = σ * Bb ^ 2 * L ^ 2 := by ring
  have h10 : R * (Bb * (2 * e0 * (2 * L ^ 2))) = 4 * e0 * Bb * R * L ^ 2 := by ring
  linarith

end CalderonN.FixedTube
