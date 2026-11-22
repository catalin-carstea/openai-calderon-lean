module

public import Proof.CalderonN.Piola
public import Proof.CalderonN.SpherePolarIntegration

import Proof.CalderonN.IntervalDistributionConstancy
import Proof.CalderonN.GreenWeak
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem integral_test_coordinate_divergence {W : (X dim) → (X dim)} (hW : ContDiff ℝ ∞ W)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, φ x * coordinateFluxDivergence W x) = -∫ x, fderiv ℝ φ x (W x) := by
  let w (i : (I dim)) (x : (X dim)) := W x i
  have hw (i : (I dim)) : ContDiff ℝ ∞ (w i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hW
  have hdc {f : (X dim) → ℝ} (h : ContDiff ℝ ∞ f) (i : (I dim)) : Continuous (coordDeriv i f) :=
    ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hi₁ (i : (I dim)) : Integrable (fun x => φ x * coordDeriv i (w i) x) :=
    (hφ.continuous.mul (hdc (hw i) i)).integrable_of_hasCompactSupport hφc.mul_right
  have hi₂ (i : (I dim)) : Integrable (fun x => w i x * coordDeriv i φ x) :=
    ((hw i).continuous.mul (hdc hφ i)).integrable_of_hasCompactSupport
      (hφc.fderiv_apply ℝ (axis i)).mul_left
  have hPart (i : (I dim)) : (∫ x, φ x * coordDeriv i (w i) x) = -∫ x, w i x * coordDeriv i φ x := by
    have h := integral_mul_coordDeriv_eq_neg isOpen_univ (hw i).contDiffOn hφ hφc (subset_univ _) i
    rw [show (fun x => coordDeriv i (w i) x * φ x) = (fun x => φ x * coordDeriv i (w i) x) from
      funext (fun _ => mul_comm _ _)] at h
    linarith
  have hsum (x : (X dim)) : (∑ i : (I dim), w i x * coordDeriv i φ x) = fderiv ℝ φ x (W x) := by
    conv_rhs => rw [← vector_eq_sum_axis (W x)]
    simp only [w,coordDeriv,map_sum,map_smul,smul_eq_mul]
  unfold coordinateFluxDivergence
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi₁ i)]
  change (∑ i : (I dim), ∫ x, φ x * coordDeriv i (w i) x) = _
  simp_rw [hPart]
  rw [Finset.sum_neg_distrib]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi₂ i)]
  simp_rw [hsum]

private theorem contDiff_normSquareRadialTest (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun x : (X dim) => χ (‖x‖^2)) :=
  hχ.comp (contDiff_norm_sq ℝ)

private theorem hasCompactSupport_normSquareRadialTest (χ : ℝ → ℝ)
    (R : ℝ) (hR : 0 < R) (hχ0 : ∀ t, R^2 ≤ t → χ t = 0) :
    HasCompactSupport (fun x : (X dim) => χ (‖x‖^2)) := by
  refine (isCompact_closedBall (0 : (X dim)) R).of_isClosed_subset (isClosed_tsupport _) ?_
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra hn
  have hxR : R < ‖x‖ := lt_of_not_ge fun h => hn (mem_closedBall_zero_iff.mpr h)
  exact hx (hχ0 _ (pow_le_pow_left₀ hR.le hxR.le 2))

private theorem fderiv_normSquareRadialTest_apply (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (x v : (X dim)) :
    fderiv ℝ (fun z : (X dim) => χ (‖z‖^2)) x v = (2 * deriv χ (‖x‖^2)) * ⟪x,v⟫_ℝ := by
  have h := ((hχ.differentiable (by simp) (‖x‖^2)).hasDerivAt.hasFDerivAt.comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).fderiv
  rw [show (fun z : (X dim) => χ (‖z‖^2)) = χ ∘ (fun z : (X dim) => ‖z‖^2) from rfl, h]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply,smul_eq_mul]
  change (2 : ℕ) • ⟪x,v⟫_ℝ * deriv χ (‖x‖^2) = _
  rw [two_nsmul]
  ring

private def radialSphereFlux (W : (X dim) → (X dim)) (r : ℝ) : ℝ :=
  r^(dim-1) * ∫ w : ↥(sphere (0 : (X dim)) 1), ⟪(w : (X dim)),W (r • (w : (X dim)))⟫_ℝ ∂(chartSurfaceMeasure dim)

private def radialDivergenceProfile (W : (X dim) → (X dim)) (r : ℝ) : ℝ :=
  r^(dim-1) * ∫ w : ↥(sphere (0 : (X dim)) 1), coordinateFluxDivergence W (r • (w : (X dim))) ∂(chartSurfaceMeasure dim)

private theorem integral_test_radial_profiles {W : (X dim) → (X dim)} (hW : ContDiff ℝ ∞ W)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : ℝ} (hR : 0 < R)
    (hχ0 : ∀ t, R^2 ≤ t → χ t = 0) :
    (∫ r in Ioi (0 : ℝ), χ (r^2) * radialDivergenceProfile W r) =
      -(∫ r in Ioi (0 : ℝ), (2*r*deriv χ (r^2)) * radialSphereFlux W r) := by
  let φ := fun x : (X dim) => χ (‖x‖^2)
  have hφ : ContDiff ℝ ∞ φ := contDiff_normSquareRadialTest χ hχ
  have hφc : HasCompactSupport φ := hasCompactSupport_normSquareRadialTest χ R hR hχ0
  have hD : Continuous (coordinateFluxDivergence W) := by
    unfold coordinateFluxDivergence coordDeriv
    exact continuous_finsetSum _ fun i _ =>
      ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hW).fderiv_right (m := ∞)
        (by simp)).clm_apply contDiff_const).continuous
  have hi₁ : Integrable (fun x => φ x * coordinateFluxDivergence W x) :=
    (hφ.continuous.mul hD).integrable_of_hasCompactSupport hφc.mul_right
  have hComp : HasCompactSupport (fun x => fderiv ℝ φ x (W x)) :=
    (hφc.fderiv ℝ).of_isClosed_subset (isClosed_tsupport _) (closure_minimal
      (fun x hx => subset_tsupport _ (fun hz => hx (by
        change fderiv ℝ φ x (W x) = 0
        rw [hz,zero_apply]))) (isClosed_tsupport _))
  have hi₂ : Integrable (fun x => fderiv ℝ φ x (W x)) :=
    (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hW).continuous).integrable_of_hasCompactSupport
      hComp
  have h := integral_test_coordinate_divergence hW hφ hφc
  rw [integral_eq_integral_Ioi_surface _ hi₁,integral_eq_integral_Ioi_surface _ hi₂] at h
  have hnorm (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) (w : ↥(sphere (0 : (X dim)) 1)) : ‖r • (w : (X dim))‖ = r := by
    rw [norm_smul,mem_sphere_zero_iff_norm.mp w.property,mul_one,Real.norm_of_nonneg (le_of_lt hr)]
  have hl : (∫ r in Ioi (0 : ℝ), r^(dim-1) *
      ∫ w : ↥(sphere (0 : (X dim)) 1), φ (r • (w : (X dim))) * coordinateFluxDivergence W (r • (w : (X dim)))
        ∂(chartSurfaceMeasure dim)) =
      ∫ r in Ioi (0 : ℝ), χ (r^2) * radialDivergenceProfile W r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp_rw [φ,hnorm r hr,integral_const_mul,radialDivergenceProfile]
    ring
  have hr : (∫ r in Ioi (0 : ℝ), r^(dim-1) *
      ∫ w : ↥(sphere (0 : (X dim)) 1), fderiv ℝ φ (r • (w : (X dim))) (W (r • (w : (X dim)))) ∂(chartSurfaceMeasure dim)) =
      ∫ r in Ioi (0 : ℝ), (2*r*deriv χ (r^2)) * radialSphereFlux W r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp_rw [φ,fderiv_normSquareRadialTest_apply χ hχ,hnorm r hr,real_inner_smul_left,
      ← mul_assoc,integral_const_mul,radialSphereFlux]
    ring
  exact hl.symm.trans (h.trans (congrArg Neg.neg hr))

/-! The scalar radial profiles below follow the released 
`Proof/Archive/ActualRadialTestProfiles.lean`. -/

private def normSquareRadialProfile (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ψ (Real.sqrt t)

private theorem contDiff_normSquareRadialProfile (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    ContDiff ℝ ∞ (normSquareRadialProfile ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : Real.sqrt t ∈ tsupport ψ
  · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht).1
    exact hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')
  · have hev : ∀ᶠ s in 𝓝 t, normSquareRadialProfile ψ s = 0 := by
      have hs : ∀ᶠ s in 𝓝 t, Real.sqrt s ∉ tsupport ψ :=
        Real.continuous_sqrt.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
      filter_upwards [hs] with s hs'
      change ψ (Real.sqrt s) = 0
      exact image_eq_zero_of_notMem_tsupport hs'
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

private theorem normSquareRadialProfile_zero_of_radius_le (ψ : ℝ → ℝ)
    (R : ℝ) (hR : 0 < R) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R)
    (t : ℝ) (ht : R^2 ≤ t) : normSquareRadialProfile ψ t = 0 := by
  have hRt : R ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt ht
  change ψ (Real.sqrt t) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => (hψs h).2.not_ge hRt)

private theorem normSquareRadialProfile_sq (ψ : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    normSquareRadialProfile ψ (r^2) = ψ r := by
  simp only [normSquareRadialProfile, Real.sqrt_sq hr]

private theorem deriv_normSquareRadialProfile_sq (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R)
    (r : ℝ) (hr : 0 < r) :
    2 * r * deriv (normSquareRadialProfile ψ) (r^2) = deriv ψ r := by
  have hχ := contDiff_normSquareRadialProfile ψ hψ R hψs
  have hev : (fun s : ℝ => normSquareRadialProfile ψ (s^2)) =ᶠ[𝓝 r] ψ := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact normSquareRadialProfile_sq ψ s (le_of_lt hs)
  have hd := (hχ.differentiable (by simp) (r^2)).hasDerivAt.comp r
    (hasDerivAt_pow 2 r)
  have hder : deriv (fun s : ℝ => normSquareRadialProfile ψ (s^2)) r = deriv ψ r :=
    hev.deriv_eq
  change deriv (normSquareRadialProfile ψ ∘ fun s : ℝ => s^2) r = deriv ψ r at hder
  rw [hd.deriv] at hder
  norm_num at hder
  nlinarith [hder]


private theorem continuousOn_surfaceIntegral_smul (f : (X dim) → ℝ) (R : ℝ)
    (hf : ContinuousOn f (closedBall (0 : (X dim)) R)) :
    ContinuousOn (fun r : ℝ => ∫ w : ↥(sphere (0 : (X dim)) 1), f (r • w.val) ∂(chartSurfaceMeasure dim))
      (Icc (0 : ℝ) R) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : (X dim)) R).exists_bound_of_continuousOn hf
  have hmem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) (w : ↥(sphere (0 : (X dim)) 1)) :
      r • w.val ∈ closedBall (0 : (X dim)) R := by
    rw [mem_closedBall_zero_iff, norm_smul, (mem_sphere_zero_iff_norm.mp w.property), mul_one,
      Real.norm_of_nonneg hr.1]
    exact hr.2
  apply continuousOn_of_dominated (μ := (chartSurfaceMeasure dim))
    (F := fun r : ℝ => fun w : ↥(sphere (0 : (X dim)) 1) => f (r • w.val))
    (bound := fun _ : ↥(sphere (0 : (X dim)) 1) => C)
  · intro r hr
    have hscale : Continuous (fun w : ↥(sphere (0 : (X dim)) 1) => r • w.val) :=
      (continuous_const : Continuous (fun _ : ↥(sphere (0 : (X dim)) 1) => r)).smul
        (continuous_subtype_val : Continuous (fun x : ↥(sphere (0 : (X dim)) 1) => (x.val : (X dim))))
    have hc : Continuous (fun w : ↥(sphere (0 : (X dim)) 1) => f (r • w.val)) :=
      hf.comp_continuous hscale (hmem r hr)
    exact hc.aestronglyMeasurable (μ := (chartSurfaceMeasure dim))
  · intro r hr
    exact ae_of_all (chartSurfaceMeasure dim) fun w => hC _ (hmem r hr w)
  · exact integrable_const (μ := (chartSurfaceMeasure dim)) C
  · apply ae_of_all (chartSurfaceMeasure dim)
    intro w
    exact hf.comp (continuous_id.smul continuous_const).continuousOn
      (fun r hr => hmem r hr w)

private theorem continuousOn_radialSphereFlux (V : (X dim) → (X dim)) (hV : Continuous V) (R : ℝ) :
    ContinuousOn (radialSphereFlux V) (Icc (0 : ℝ) R) := by
  have hq : Continuous (fun x : (X dim) => ⟪x,V x⟫_ℝ) := continuous_id.inner hV
  have hi := continuousOn_surfaceIntegral_smul (fun x : (X dim) => ⟪x,V x⟫_ℝ) R hq.continuousOn
  have he : radialSphereFlux V = (fun r : ℝ => r^(dim-2) *
      ∫ w : ↥(sphere (0 : (X dim)) 1), ⟪r • w.val,V (r • w.val)⟫_ℝ ∂(chartSurfaceMeasure dim)) := by
    funext r
    unfold radialSphereFlux
    simp_rw [real_inner_smul_left]
    rw [integral_const_mul]
    have hn : 2 ≤ dim := Fin.nontrivial_iff_two_le.mp inferInstance
    have hp : dim-1 = dim-2+1 := by omega
    rw [hp, pow_succ]
    ring
  rw [he]
  exact (continuousOn_id.pow (dim-2)).mul hi

private theorem integral_test_radialSphereFlux {W : (X dim) → (X dim)} (hW : ContDiff ℝ ∞ W)
    {R : ℝ} (hR : 0 < R) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    (∫ r, ψ r * radialDivergenceProfile W r) = -(∫ r, deriv ψ r * radialSphereFlux W r) := by
  let χ := normSquareRadialProfile ψ
  have hχ := contDiff_normSquareRadialProfile ψ hψ R hψs
  have h := integral_test_radial_profiles hW hχ hR
    (normSquareRadialProfile_zero_of_radius_le ψ R hR hψs)
  have hL : (∫ r in Ioi (0 : ℝ), χ (r^2) * radialDivergenceProfile W r) =
      ∫ r, ψ r * radialDivergenceProfile W r := by
    refine (setIntegral_congr_fun (g := fun r => ψ r * radialDivergenceProfile W r)
      measurableSet_Ioi (fun r hr => ?_)).trans ?_
    · rw [show χ (r^2) = ψ r from normSquareRadialProfile_sq ψ r hr.le]
    · exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr =>
        mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun ht => hr (hψs ht).1)) _)
  have hQ : (∫ r in Ioi (0 : ℝ), (2*r*deriv χ (r^2)) * radialSphereFlux W r) =
      ∫ r, deriv ψ r * radialSphereFlux W r := by
    refine (setIntegral_congr_fun (g := fun r => deriv ψ r * radialSphereFlux W r)
      measurableSet_Ioi (fun r hr => ?_)).trans ?_
    · rw [show 2*r*deriv χ (r^2) = deriv ψ r from deriv_normSquareRadialProfile_sq ψ hψ R hψs r hr]
    · exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr =>
        mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun ht => hr (hψs (tsupport_deriv_subset ht)).1)) _)
  rwa [hL,hQ] at h

private theorem continuous_coordinateFluxDivergence {W : (X dim) → (X dim)} (hW : ContDiff ℝ ∞ W) :
    Continuous (coordinateFluxDivergence W) := by
  unfold coordinateFluxDivergence coordDeriv
  exact continuous_finsetSum _ fun i _ =>
    ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hW).fderiv_right (m := ∞)
      (by simp)).clm_apply contDiff_const).continuous

private theorem integrable_test_mul_continuousOn {U : Set ℝ} (hU : IsOpen U)
    {f p : ℝ → ℝ} (hf : Continuous f) (hfC : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hp : ContinuousOn p U) : Integrable (fun x => f x * p x) := by
  exact ((hf.continuousOn.mul hp).continuous_of_tsupport_subset hU
    ((tsupport_mul_subset_left (f := f) (g := p)).trans hfU)).integrable_of_hasCompactSupport hfC.mul_right

private theorem radialSphereFlux_eq_integral_divergenceProfile
    {W : (X dim) → (X dim)} (hW : ContDiff ℝ ∞ W) {R : ℝ} (hR : 0 < R) :
    radialSphereFlux W R = ∫ r in (0 : ℝ)..R, radialDivergenceProfile W r := by
  let D := radialDivergenceProfile W
  let Q := radialSphereFlux W
  let P (r : ℝ) := ∫ s in (0 : ℝ)..r, D s
  let U := Ioo (0 : ℝ) R
  have hD : ContinuousOn D (Icc (0 : ℝ) R) :=
    (continuousOn_id.pow (dim-1)).mul (continuousOn_surfaceIntegral_smul _ _
      (continuous_coordinateFluxDivergence hW).continuousOn)
  have hQ : ContinuousOn Q (Icc (0 : ℝ) R) := continuousOn_radialSphereFlux W hW.continuous R
  have hP : ContinuousOn P (Icc (0 : ℝ) R) := by
    have hi : IntegrableOn D (uIcc (0 : ℝ) R) := by
      rw [uIcc_of_le hR.le]
      exact hD.integrableOn_compact isCompact_Icc
    simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval hi
  have hPD (r : ℝ) (hr : r ∈ U) : HasDerivAt P (D r) r := by
    have hint : IntervalIntegrable D volume 0 r :=
      (hD.mono (Icc_subset_Icc le_rfl hr.2.le)).intervalIntegrable_of_Icc hr.1.le
    have hc : ContinuousAt D r := hD.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hm : StronglyMeasurableAtFilter D (𝓝 r) (volume : Measure ℝ) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hD.mono Ioo_subset_Icc_self) r hr
    exact intervalIntegral.integral_hasDerivAt_right hint hm hc
  have hDiv (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
      (∫ r, deriv ψ r * P r) = -(∫ r, ψ r * D r) := by
    have hψc : HasCompactSupport ψ :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hψU.trans Ioo_subset_Icc_self)
    have hψdU := (tsupport_deriv_subset (f := ψ)).trans hψU
    have hDl : (fun r => fderiv ℝ P r (1 : ℝ) * ψ r) = fun r => ψ r * D r := by
      funext r
      by_cases hr : r ∈ U
      · rw [fderiv_apply_one_eq_deriv,(hPD r hr).deriv,mul_comm]
      · have hz : ψ r = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hr (hψU ht))
        rw [hz,mul_zero,zero_mul]
    have hPl : (fun r => P r * fderiv ℝ ψ r (1 : ℝ)) = fun r => deriv ψ r * P r :=
      funext (fun r => by rw [fderiv_apply_one_eq_deriv,mul_comm])
    have hi₁ : Integrable (fun r => fderiv ℝ P r (1 : ℝ) * ψ r) := by
      rw [hDl]
      exact integrable_test_mul_continuousOn isOpen_Ioo hψ.continuous hψc hψU (hD.mono Ioo_subset_Icc_self)
    have hi₂ : Integrable (fun r => P r * fderiv ℝ ψ r (1 : ℝ)) := by
      rw [hPl]
      exact integrable_test_mul_continuousOn isOpen_Ioo (hψ.continuous_deriv (by simp))
        hψc.deriv hψdU (hP.mono Ioo_subset_Icc_self)
    have hi₃ : Integrable (fun r => P r * ψ r) :=
      (integrable_test_mul_continuousOn isOpen_Ioo hψ.continuous hψc hψU (hP.mono Ioo_subset_Icc_self)).congr
        (Eventually.of_forall fun _ => mul_comm _ _)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
      (fun r hr => (hPD r (hψU hr)).differentiableAt)
      (fun r _ => hψ.differentiable (by simp) r)
    rwa [hPl,hDl] at h
  have hQP := (hQ.sub hP).mono Ioo_subset_Icc_self
  have hDist (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
      ∫ x, deriv ψ x • (Q x-P x) = 0 := by
    have hψc : HasCompactSupport ψ :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hψU.trans Ioo_subset_Icc_self)
    have hψdU := (tsupport_deriv_subset (f := ψ)).trans hψU
    have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) R)) :
        Integrable (fun x => deriv ψ x * f x) :=
      integrable_test_mul_continuousOn isOpen_Ioo (hψ.continuous_deriv (by simp))
        hψc.deriv hψdU (hf.mono Ioo_subset_Icc_self)
    have h₁ := integral_test_radialSphereFlux hW hR hψ hψU
    have h₂ := hDiv ψ hψ hψU
    change (∫ x, deriv ψ x * (Q x-P x)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hi Q hQ) (hi P hP)]
    linarith
  obtain ⟨c,hc⟩ := exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero hQP hDist
  have hExt : EqOn (fun r => Q r-P r) (fun _ => c) (Icc (0 : ℝ) R) :=
    hc.of_subset_closure (hQ.sub hP) continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hR.ne])
  have hc0 : c = 0 := by
    have hz := hExt (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl,hR.le⟩)
    simpa only [Q,P,radialSphereFlux,zero_pow (by have hd := Fin.nontrivial_iff_two_le.mp (inferInstance : Nontrivial (Fin dim)); omega : dim-1 ≠ 0),zero_mul,
      intervalIntegral.integral_same,sub_zero] using hz.symm
  exact sub_eq_zero.mp (by simpa only [hc0] using hExt (show R ∈ Icc 0 R from ⟨hR.le,le_rfl⟩))

/-- The divergence theorem on the unit ball, with the chart's Haar
surface measure and the outward Euclidean unit normal. -/
theorem integral_unitBall_coordinateFluxDivergence (W : (X dim) → (X dim)) (hW : ContDiff ℝ ∞ W) :
    (∫ x in ball (0 : (X dim)) 1, coordinateFluxDivergence W x) = unitSphereFlux W := by
  have hi : IntegrableOn (coordinateFluxDivergence W) (ball (0 : (X dim)) 1) :=
    ((continuous_coordinateFluxDivergence hW).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : (X dim)) 1)).mono_set ball_subset_closedBall
  rw [integral_ball_zero_eq_radial_interval _ _ one_pos hi]
  change (∫ r in (0 : ℝ)..1, radialDivergenceProfile W r) = _
  rw [← radialSphereFlux_eq_integral_divergenceProfile hW one_pos]
  simp only [radialSphereFlux,unitSphereFlux,one_pow,one_mul,one_smul]

end CalderonN
