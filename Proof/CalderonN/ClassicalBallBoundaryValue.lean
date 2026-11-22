module

public import Proof.CalderonN.BallRegularity.CoordinateWeakIntegration
public import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev
public import Proof.CalderonN.SmoothBallDivergence
public import Proof.CalderonN.NormalFluxDensity

import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Gradient InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]


open CalderonN.BallDirichlet

theorem unitBallCoordinateGradientL_smooth_ae (b : (SmoothData dim)) (i : (I dim)) :
    unitBallCoordinateGradientL i (smoothSobolev b) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      coordDeriv i b.1 := by
  filter_upwards [unitBallCoordinateGradientL_ae i (smoothSobolev b),
    gradient_smoothSobolev_ae b] with x hx hgrad
  rw [hx,hgrad,coordDeriv,← inner_gradient_left]
  simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]

set_option maxHeartbeats 1200000 in
/-- A smooth representative of an element of the zero Dirichlet space has
zero trace pointwise. Test the weak integration by parts formula with
the components of the vector field (b x), then integrate the outward flux
of (b² x) on the actual sphere. -/
theorem eqOn_zero_sphere_of_ballH1Zero [Nontrivial (Fin dim)]
    {b : (X dim) → ℝ} (hb : ContDiff ℝ ∞ b) (v : (FixedBallH1Zero dim))
    (hv : TauCeti.W1p.value (v : (FixedBallH1 dim)) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] b) :
    EqOn b 0 (standardSphere dim) := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let S : (SmoothData dim) := ⟨b,hb⟩
  have hvS : (v : (FixedBallH1 dim)) = smoothSobolev S := by
    apply TauCeti.W1p.ext_value
    exact Lp.ext (hv.trans (value_smoothSobolev_ae S).symm)
  let a (i : (I dim)) : (SmoothData dim) :=
    ⟨fun x => b x * x i,hb.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff⟩
  have hWeak (i : (I dim)) := unitBall_coordinate_inner_integration (smoothSobolev (a i)) i v
  have hFirst (i : (I dim)) : ⟪unitBallCoordinateGradientL i (smoothSobolev (a i)),
      TauCeti.W1p.value (v : (FixedBallH1 dim))⟫_ℝ = ∫ x, b x * coordDeriv i (a i).1 x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_smooth_ae (a i) i,hv] with x hd hx
    simp only [RCLike.inner_apply,conj_trivial,hd,hx]
  have hSecond (i : (I dim)) : ⟪TauCeti.W1p.value (smoothSobolev (a i)),
      unitBallCoordinateGradientL i (v : (FixedBallH1 dim))⟫_ℝ = ∫ x, coordDeriv i b x * (a i).1 x ∂μ := by
    rw [hvS,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_smooth_ae S i,value_smoothSobolev_ae (a i)] with x hd hx
    simp only [RCLike.inner_apply,conj_trivial,hd,hx,S]
  let W (x : (X dim)) := (b x)^2 • x
  have hW : ContDiff ℝ ∞ W := (hb.pow 2).smul contDiff_id
  have hWprod (i : (I dim)) (x : (X dim)) : W x i = b x * (a i).1 x := by
    simp [W,a,pow_two,mul_assoc]
  have hWderiv (i : (I dim)) (x : (X dim)) : coordDeriv i (fun z => W z i) x =
      b x * coordDeriv i (a i).1 x + coordDeriv i b x * (a i).1 x := by
    simp only [hWprod,coordDeriv]
    rw [fderiv_fun_mul (hb.differentiable (by simp) x) ((a i).2.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hInt (f : (X dim) → ℝ) (h : Continuous f) : Integrable f μ :=
    (h.continuousOn.integrableOn_compact (isCompact_closedBall (0 : (X dim)) 1)).mono_set ball_subset_closedBall
  have hD (u : (SmoothData dim)) (i : (I dim)) : Continuous (coordDeriv i u.1) :=
    ((u.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hInt' (i : (I dim)) : (∫ x, coordDeriv i (fun z => W z i) x ∂μ) = 0 := by
    simp_rw [hWderiv]
    have hI₁ : Integrable (fun x => b x * coordDeriv i (a i).1 x) μ :=
      hInt _ (hb.continuous.mul (hD (a i) i))
    have hI₂ : Integrable (fun x => coordDeriv i b x * (a i).1 x) μ :=
      hInt _ ((hD S i).mul (a i).2.continuous)
    rw [integral_add hI₁ hI₂]
    have h := hWeak i
    rw [hFirst,hSecond] at h
    linarith only [h]
  have hFlux : unitSphereFlux W = 0 := by
    rw [← integral_unitBall_coordinateFluxDivergence W hW]
    change (∫ x, ∑ i, coordDeriv i (fun z => W z i) x ∂μ) = 0
    rw [integral_finsetSum _ (fun i _ => hInt _ (hD ⟨fun z => W z i,
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hW⟩ i))]
    simp only [hInt',Finset.sum_const_zero]
  have hSurface : (∫ w : ↥(sphere (0 : (X dim)) 1), (b w)^2 ∂(chartSurfaceMeasure dim)) = 0 := by
    rw [← hFlux]
    apply integral_congr_ae
    filter_upwards with w
    have hw : ‖(w : (X dim))‖ = 1 := by
      simpa only [standardSphere,mem_sphere,dist_zero_right] using w.property
    change (b w)^2 = ⟪(w : (X dim)),(b w)^2 • (w : (X dim))⟫_ℝ
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hw,one_pow,mul_one]
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  have hC : Continuous (fun w : ↥(standardSphere dim) => b w) := hb.continuous.comp continuous_subtype_val
  have hSphere : (∫ w : ↥(standardSphere dim), (b w)^2 ∂(sphereProbability dim)) = 0 := by
    have h := integral_unitSphereArea_mul_probability (dim := dim) (fun w => (b w)^2)
    rw [integral_const_mul,hSurface] at h
    exact (mul_eq_zero.mp h).resolve_left (unitSphereArea_pos (dim := dim)).ne'
  let : (sphereProbability dim).IsOpenPosMeasure := by
    let σ := (volume : Measure (X dim)).toSphere
    have h0 : σ univ ≠ 0 := by
      rw [ne_eq,Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    change (((σ univ)⁻¹) • σ).IsOpenPosMeasure
    exact Measure.isOpenPosMeasure_smul σ (by simp [measure_ne_top σ univ])
  have hSq : Integrable (fun w : ↥(standardSphere dim) => (b w)^2) (sphereProbability dim) :=
    (hC.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAE : (fun w : ↥(standardSphere dim) => b w)  =ᵐ[(sphereProbability dim)] (fun _ => (0 : ℝ)) := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun w : ↥(standardSphere dim) => sq_nonneg (b w)) hSq).mp hSphere]
      with w hw
    exact sq_eq_zero_iff.mp hw
  have h := Measure.eqOn_open_of_ae_eq (μ := (sphereProbability dim))
    (by simpa only [Measure.restrict_univ] using hAE) isOpen_univ hC.continuousOn continuousOn_const
  exact fun w hw => h (mem_univ (⟨w,hw⟩ : ↥(standardSphere dim)))

end CalderonN
