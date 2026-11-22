module

public import Proof.CalderonN.MovingTrace
public import Mathlib.Geometry.Manifold.Instances.Sphere

import Proof.CalderonN.FixedKernelIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure CalderonN
open scoped ContDiff Topology ENNReal NNReal

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

/-- The total stereographic coordinate function is measurable, since it is
continuous away from its single pole. -/
theorem measurable_stereographic_coordinates (v : ↥(sphere (0 : X dim) 1)) :
    Measurable (stereographic' (dim-1) v) := by
  apply measurable_of_continuousOn_compl_singleton v
  rw [← stereographic'_source (n := dim-1) v]
  exact (stereographic' (dim-1) v).continuousOn

private theorem contDiff_det_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ContDiff ℝ ∞ (fun f : E →L[ℝ] E => f.det) := by
  classical
  let b := Module.finBasis ℝ E
  simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
  rw [show (fun f : E →L[ℝ] E => ((LinearMap.toMatrix b b) f.toLinearMap).det) =
      fun f => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) * ∏ i, (LinearMap.toMatrix b b f.toLinearMap) (σ i) i by
    funext f
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]]
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  simp only [LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  exact (((b.coord (σ i)).comp ((ContinuousLinearMap.apply ℝ E (b i)).toLinearMap)).toContinuousLinearMap).contDiff

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
/-- Integration of the radial Jacobian on a compactly carried shell has
strictly positive, smooth angular density. -/
private theorem positive_smooth_shellJacobian
    {Φ : X (dim-1) × ℝ → X (dim-1) × ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hDet : ∀ q : X (dim-1) × ℝ, 0 < q.2 → (fderiv ℝ Φ q).det ≠ 0) :
    let J (x : X (dim-1)) := ∫ r in Ico (1/2 : ℝ) (3/4), |(fderiv ℝ Φ (x,r)).det|
    ContDiff ℝ ∞ J ∧ ∀ x, 0 < J x := by
  let S := Ico (1/2 : ℝ) (3/4)
  let K := Icc (1/2 : ℝ) (3/4)
  let D (p : X (dim-1) × ℝ) := |(fderiv ℝ Φ p).det|
  have hSmoothDet : ContDiff ℝ ∞ (fun q => (fderiv ℝ Φ q).det) :=
    contDiff_det_clm.comp (hΦ.fderiv_right (by simp))
  have hSmoothD : ContDiffOn ℝ ∞ D (univ ×ˢ Ioi (0 : ℝ)) :=
    hSmoothDet.contDiffOn.abs fun q hq => hDet q hq.2
  have hD : Continuous D := hSmoothDet.continuous.abs
  change ContDiff ℝ ∞ (fun x => ∫ r in S, D (x,r)) ∧ ∀ x, 0 < ∫ r in S, D (x,r)
  constructor
  · let μ : Measure ℝ := volume.restrict S
    have : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ico _ _
    have hμ : μ Kᶜ = 0 := by
      rw [show μ = volume.restrict S from rfl, Measure.restrict_apply (isClosed_Icc.measurableSet.compl)]
      have he : Kᶜ ∩ S = ∅ := Set.disjoint_iff_inter_eq_empty.mp
        (disjoint_compl_left_iff_subset.mpr Ico_subset_Icc_self)
      rw [he, measure_empty]
    have hD' : ContDiffOn ℝ ∞ (fun q : ℝ × X (dim-1) => D q.swap) (Ioi 0 ×ˢ univ) :=
      hSmoothD.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)
    apply contDiffOn_univ.mp
    apply contDiffOn_infty.mpr
    intro n
    exact contDiffOn_integral_on_compact (μ := μ) isCompact_Icc
      (fun _ hr => (by norm_num : (0:ℝ) < 1/2).trans_le hr.1) isOpen_Ioi isOpen_univ hμ n
      (fun r x => D (x,r)) (hD'.of_le (by simp))
  · intro x
    have hInt : IntegrableOn (fun r => D (x,r)) S :=
      ((hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (μ := volume) isCompact_Icc).mono_set Ico_subset_Icc_self
    apply (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall (fun r => abs_nonneg _)) hInt).mpr
    have hSupp : S ⊆ Function.support (fun r => D (x,r)) := by
      intro r hr
      exact abs_ne_zero.mpr (hDet (x,r) ((by norm_num : (0:ℝ) < 1/2).trans_le hr.1))
    rw [Set.inter_eq_self_of_subset_right hSupp, Real.volume_Ico]
    norm_num

/-- The normalized sphere measure in a stereographic chart is Euclidean
volume with a smooth positive density. The radial map is required only
through its smoothness, injectivity and the nonvanishing Jacobian. -/
theorem exists_stereographic_map_sphereProbability_eq_withDensity_of_radialMap
    (v : ↥(sphere (0 : X dim) 1))
    (e : X dim ≃L[ℝ] (X (dim-1) × ℝ))
    (Φ : X (dim-1) × ℝ → X (dim-1) × ℝ)
    (hEq : ∀ q, Φ q = e (q.2 • ((stereographic' (dim-1) v).symm q.1 : X dim)))
    (hΦ : ContDiff ℝ ∞ Φ)
    (hInj : InjOn Φ (univ ×ˢ Ioi (0 : ℝ)))
    (hDet : ∀ q, 0 < q.2 → (fderiv ℝ Φ q).det ≠ 0) :
    ∃ w : X (dim-1) → ℝ, ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
      Measure.map (stereographic' (dim-1) v)
        ((sphereProbability dim).restrict (stereographic' (dim-1) v).source) =
        (volume : Measure (X (dim-1))).withDensity (fun x => ENNReal.ofReal (w x)) := by
  let κ := stereographic' (dim-1) v
  let a : Ioi (0 : ℝ) := ⟨1/2, by norm_num⟩
  let b : Ioi (0 : ℝ) := ⟨3/4, by norm_num⟩
  let S := Ico (1/2 : ℝ) (3/4)
  let Q := Iio b \ Iio a
  have hQ (r : Ioi (0 : ℝ)) : r ∈ Q ↔ (r : ℝ) ∈ S := by
    change ((r : ℝ) < 3/4 ∧ ¬ (r : ℝ) < 1/2) ↔ (1/2 : ℝ) ≤ r ∧ (r : ℝ) < 3/4
    rw [not_lt, and_comm]
  let μ := (volume : Measure (X dim)).toSphere
  let ν := Measure.volumeIoiPow (dim-1)
  let μ₀ : Measure (X dim) := volume
  let μ₁ : Measure (X (dim-1) × ℝ) := (volume : Measure (X (dim-1))).prod (volume : Measure ℝ)
  have : μ₁.IsAddHaarMeasure := inferInstanceAs
    (((volume : Measure (X (dim-1))).prod (volume : Measure ℝ)).IsAddHaarMeasure)
  have hνa : ν (Iio a) = ENNReal.ofReal ((1/2 : ℝ)^((dim-1)+1) / ((dim-1)+1 : ℕ)) :=
    by simpa only [ν,a,Nat.cast_add,Nat.cast_one] using Measure.volumeIoiPow_apply_Iio (dim-1) a
  have hνb : ν (Iio b) = ENNReal.ofReal ((3/4 : ℝ)^((dim-1)+1) / ((dim-1)+1 : ℕ)) :=
    by simpa only [ν,b,Nat.cast_add,Nat.cast_one] using Measure.volumeIoiPow_apply_Iio (dim-1) b
  have hνlt : ν (Iio a) < ν (Iio b) := by
    rw [hνa,hνb]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (pow_lt_pow_left₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero _)) (by positivity))
  have hνQ : ν Q ≠ 0 := by
    rw [show ν Q = ν (Iio b) - ν (Iio a) from
      measure_sdiff (Iio_subset_Iio (by norm_num [a,b])) (measurableSet_Iio : MeasurableSet (Iio a)).nullMeasurableSet (hνlt.trans_le le_top).ne]
    exact (tsub_pos_of_lt hνlt).ne'
  have hνQ' : ν Q ≠ ⊤ :=
    ((measure_mono (sdiff_subset : Q ⊆ Iio b)).trans_lt (hνb ▸ ENNReal.ofReal_lt_top)).ne
  have hμ₀ : μ univ ≠ 0 := by
    have : Nontrivial (X dim) := ⟨⟨v,0,ne_zero_of_mem_unit_sphere v⟩⟩
    exact fun h => μ₀.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp h)
  have hμ₀' : μ univ ≠ ⊤ := measure_lt_top μ univ |>.ne
  have : IsAddHaarMeasure (μ₀.map e) := e.isAddHaarMeasure_map μ₀
  let c : ℝ≥0∞ := addHaarScalarFactor (μ₀.map e) μ₁
  have hc₀ : c ≠ 0 := by
    change ((addHaarScalarFactor (μ₀.map e) μ₁ : ℝ≥0) : ℝ≥0∞) ≠ 0
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ₀.map e) μ₁).ne'
  have hc₁ : c ≠ ⊤ := ENNReal.coe_ne_top
  have hc : μ₀.map e = c • μ₁ := isAddLeftInvariant_eq_smul _ _
  let α := c * (μ univ * ν Q)⁻¹
  have hαν₀ : μ univ * ν Q ≠ 0 := mul_ne_zero hμ₀ hνQ
  have hαν₁ : μ univ * ν Q ≠ ⊤ := (ENNReal.mul_lt_top hμ₀'.lt_top hνQ'.lt_top).ne
  have hα₀ : α ≠ 0 := mul_ne_zero hc₀ (ENNReal.inv_ne_zero.mpr hαν₁)
  have hα₁ : α ≠ ⊤ := (ENNReal.mul_lt_top hc₁.lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hαν₀))).ne
  let D (p : X (dim-1) × ℝ) := |(fderiv ℝ Φ p).det|
  let J (x : X (dim-1)) := ∫ r in S, D (x,r)
  obtain ⟨hJ,hJpos⟩ := positive_smooth_shellJacobian hΦ hDet
  let w (x : X (dim-1)) := α.toReal * J x
  have hw : ContDiff ℝ ∞ w := contDiff_const.mul hJ
  have hwpos : ∀ x, 0 < w x := fun x => mul_pos (ENNReal.toReal_pos hα₀ hα₁) (hJpos x)
  refine ⟨w,hw,hwpos,?_⟩
  ext B hB
  let A := κ.source ∩ κ ⁻¹' B
  have hκ := measurable_stereographic_coordinates v
  have hA : MeasurableSet A := κ.open_source.measurableSet.inter (hκ hB)
  have hBS : MeasurableSet (B ×ˢ S) := hB.prod measurableSet_Ico
  let p := homeomorphUnitSphereProd (X dim)
  have hInjBS : InjOn Φ (B ×ˢ S) := hInj.mono (fun q hq =>
    (show q ∈ (univ : Set (X (dim-1))) ×ˢ Ioi (0 : ℝ) from
      ⟨mem_univ _,(by norm_num : (0:ℝ) < 1/2).trans_le hq.2.1⟩))
  have hDeriv (q : X (dim-1) × ℝ) (_ : q ∈ B ×ˢ S) :
      HasFDerivWithinAt Φ (fderiv ℝ Φ q) (B ×ˢ S) q :=
    (hΦ.differentiable (by simp) q).hasFDerivAt.hasFDerivWithinAt
  have hZ : MeasurableSet (Φ '' (B ×ˢ S)) := measurable_image_of_fderivWithin hBS hDeriv hInjBS
  have hImage : (Subtype.val : ({(0 : X dim)}ᶜ : Set (X dim)) → X dim) '' (p ⁻¹' (A ×ˢ Q)) =
      e ⁻¹' (Φ '' (B ×ˢ S)) := by
    ext z
    constructor
    · rintro ⟨z',hz',rfl⟩
      let u := p z'
      have hu : u ∈ A ×ˢ Q := hz'
      refine ⟨(κ u.1,u.2.val),⟨hu.1.2,(hQ u.2).mp hu.2⟩,?_⟩
      have he : u.2.val • (u.1 : X dim) = (z' : X dim) := by
        calc
          _ = (p.symm u : X dim) := (homeomorphUnitSphereProd_symm_apply_coe (X dim) u).symm
          _ = _ := congrArg Subtype.val (p.symm_apply_apply z')
      rw [hEq]
      change e (u.2.val • (κ.symm (κ u.1) : X dim)) = e z'
      rw [κ.left_inv hu.1.1,he]
    · rintro ⟨⟨x,r⟩,hq,he⟩
      let q : ↥(sphere (0 : X dim) 1) × Ioi (0 : ℝ) := (κ.symm x,⟨r,(by norm_num : (0:ℝ) < 1/2).trans_le hq.2.1⟩)
      have hx : x ∈ κ.target := by simp [κ]
      have hA' : q.1 ∈ A := ⟨κ.map_target hx,by change κ (κ.symm x) ∈ B; rw [κ.right_inv hx]; exact hq.1⟩
      refine ⟨p.symm q, ?_, ?_⟩
      · change p (p.symm q) ∈ A ×ˢ Q
        rw [p.apply_symm_apply]
        exact ⟨hA',(hQ q.2).mpr hq.2⟩
      · rw [hEq] at he
        exact (homeomorphUnitSphereProd_symm_apply_coe (X dim) q).trans (e.injective he)
  have hPolar : μ₀ (e ⁻¹' (Φ '' (B ×ˢ S))) = μ A * ν Q := by
    have hMp := μ₀.measurePreserving_homeomorphUnitSphereProd
    have hM := congrArg (fun M : Measure (↥(sphere (0 : X dim) 1) × Ioi (0 : ℝ)) => M (A ×ˢ Q)) hMp.map_eq
    rw [Measure.map_apply p.measurable (hA.prod (measurableSet_Iio.diff measurableSet_Iio)),
      comap_subtype_coe_apply (measurableSet_singleton _).compl, hImage, Measure.prod_prod,
      show Module.finrank ℝ (X dim) - 1 = dim-1 by simp] at hM
    exact hM
  have hChange : (∫⁻ q in B ×ˢ S, ENNReal.ofReal (D q) ∂μ₁) = μ₁ (Φ '' (B ×ˢ S)) :=
    lintegral_abs_det_fderiv_eq_addHaar_image μ₁ hBS hDeriv hInjBS
  have hRel : μ A * ν Q = c * (∫⁻ q in B ×ˢ S, ENNReal.ofReal (D q) ∂μ₁) := by
    rw [hChange, ← hPolar, ← Measure.map_apply e.continuous.measurable hZ,
      hc, Measure.smul_apply, smul_eq_mul]
  have hΦ' : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have hD : Continuous D := (ContinuousLinearMap.continuous_det.comp hΦ'.continuous).abs
  have hRel' : μ A * ν Q = c * (∫⁻ x in B, ENNReal.ofReal (J x)) := by
    rw [hRel, show μ₁ = (volume : Measure (X (dim-1))).prod (volume : Measure ℝ) by rfl,
      setLIntegral_prod _ ((hD.measurable.ennreal_ofReal).aemeasurable)]
    congr 1
    apply lintegral_congr
    intro x
    symm
    exact ofReal_integral_eq_lintegral_ofReal
      (((hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (μ := volume) isCompact_Icc).mono_set Ico_subset_Icc_self)
      (Filter.Eventually.of_forall (fun r => abs_nonneg _))
  rw [Measure.map_apply hκ hB, Measure.restrict_apply (hκ hB), sphereProbability, Measure.smul_apply,
    smul_eq_mul, Set.inter_comm, withDensity_apply _ hB]
  change (μ univ)⁻¹ * μ A = ∫⁻ x in B, ENNReal.ofReal (α.toReal * J x)
  simp_rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hα₁]
  rw [lintegral_const_mul _ hJ.continuous.measurable.ennreal_ofReal]
  calc
    (μ univ)⁻¹ * μ A = (μ univ * ν Q)⁻¹ * (μ A * ν Q) := by
      rw [ENNReal.mul_inv (Or.inl hμ₀) (Or.inl hμ₀'), mul_mul_mul_comm, ENNReal.inv_mul_cancel hνQ hνQ', mul_one]
    _ = _ := by rw [hRel']; dsimp only [α]; ac_rfl

/-- The chart density gives the complex Bochner change of variables used for
localized moving trace operators. -/
theorem stereographic_sphereProbability_integral_of_density
    (v : ↥(sphere (0 : X dim) 1)) {w : X (dim-1) → ℝ} (hw : Continuous w)
    (hw₀ : ∀ x, 0 ≤ w x)
    (hDensity : Measure.map (stereographic' (dim-1) v)
        ((sphereProbability dim).restrict (stereographic' (dim-1) v).source) =
        (volume : Measure (X (dim-1))).withDensity (fun x => ENNReal.ofReal (w x)))
    (F : X (dim-1) → ℂ) (hF : Continuous F) :
    (∫ z in (stereographic' (dim-1) v).source, F (stereographic' (dim-1) v z) ∂sphereProbability dim) =
      ∫ x, (w x : ℂ) * F x := by
  let κ := stereographic' (dim-1) v
  let μ : Measure ↥(sphere (0 : X dim) 1) := sphereProbability dim
  change (∫ z, F (κ z) ∂(μ.restrict κ.source)) = _
  calc
    _ = ∫ x, F x ∂Measure.map κ (μ.restrict κ.source) :=
      (integral_map (μ := μ.restrict κ.source) (measurable_stereographic_coordinates v).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = _ := by
      change Measure.map κ (μ.restrict κ.source) = _ at hDensity
      rw [hDensity, integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp_rw [ENNReal.toReal_ofReal (hw₀ _), Complex.real_smul]

/-- A continuous datum vanishing at the missing pole can be integrated
on the whole sphere before applying the stereographic density. -/
theorem stereographic_sphereProbability_integral_of_supported_density
    (v : ↥(sphere (0 : X dim) 1)) {w : X (dim-1) → ℝ} (hw : Continuous w)
    (hw₀ : ∀ x, 0 ≤ w x)
    (hDensity : Measure.map (stereographic' (dim-1) v)
        ((sphereProbability dim).restrict (stereographic' (dim-1) v).source) =
        (volume : Measure (X (dim-1))).withDensity (fun x => ENNReal.ofReal (w x)))
    (F : ↥(sphere (0 : X dim) 1) → ℂ) (hF : Continuous F) (hv : F v = 0) :
    (∫ z, F z ∂sphereProbability dim) =
      ∫ x, (w x : ℂ) * F ((stereographic' (dim-1) v).symm x) := by
  let κ := stereographic' (dim-1) v
  let μ : Measure ↥(sphere (0 : X dim) 1) := sphereProbability dim
  let f (x : X (dim-1)) := F (κ.symm x)
  have hκ : Continuous κ.symm := by
    apply continuousOn_univ.mp
    simpa only [κ,OpenPartialHomeomorph.symm_source,stereographic'_target] using κ.symm.continuousOn
  have hf : Continuous f := hF.comp hκ
  have hIndicator : κ.source.indicator F = F := by
    funext z
    by_cases hz : z ∈ κ.source
    · exact indicator_of_mem hz F
    · have e : z = v := by simpa only [κ,stereographic'_source,mem_compl_iff,not_not,mem_singleton_iff] using hz
      rw [indicator_of_notMem hz, e, hv]
  change (∫ z, F z ∂μ) = ∫ x, (w x : ℂ) * f x
  calc
    _ = ∫ z in κ.source, F z ∂μ := by rw [← integral_indicator κ.open_source.measurableSet, hIndicator]
    _ = ∫ z in κ.source, f (κ z) ∂μ := by
      apply setIntegral_congr_fun κ.open_source.measurableSet
      intro z hz
      change F z = F (κ.symm (κ z))
      rw [κ.left_inv hz]
    _ = _ := stereographic_sphereProbability_integral_of_density v hw hw₀ hDensity f hf

end CalderonPaper
