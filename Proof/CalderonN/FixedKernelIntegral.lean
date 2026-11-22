module

public import Proof.CalderonN.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-! The compact domination and differentiation arguments adapt
`FixedSurfaceFluxIntegration.lean` and `FixedSurfaceTransferIntegration.lean`
from the earlier Calderón development at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ae_mem_of_measure_compl {A : Type*} [MeasurableSpace A] {μ : Measure A} {K : Set A} (h : μ Kᶜ = 0) :
    ∀ᵐ x ∂μ, x ∈ K :=
  ae_iff.2 h

omit [NormedSpace ℝ E] in
/-- Continuous functions on the compact carrier are integrable. -/
lemma integrable_of_continuousOn {A : Type*} [TopologicalSpace A] [T2Space A] [MeasurableSpace A]
    [OpensMeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ] {K : Set A}
    {f : A → E} (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hf : ContinuousOn f K) :
    Integrable f μ := by
  have h := hf.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_of_measure_compl hμ)] at h

lemma continuousOn_slice {A P F : Type*} [TopologicalSpace A] [TopologicalSpace P] [TopologicalSpace F]
    {U K : Set A} {V : Set P} {g : A → P → F}
    (hg : ContinuousOn (Function.uncurry g) (U ×ˢ V)) (hKU : K ⊆ U)
    {z : P} (hz : z ∈ V) : ContinuousOn (fun x => g x z) K :=
  hg.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hx => ⟨hKU hx, hz⟩)

/-- The partial derivative in the second variable is the joint derivative composed
with the second inclusion. -/
lemma hasFDerivAt_partial {A P : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set A} {V : Set P} {f : A → P → E} {m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hm : 1 ≤ m)
    (hU : IsOpen U) (hV : IsOpen V) {x : A} {z : P} (hx : x ∈ U) (hz : z ∈ V) :
    HasFDerivAt (f x) ((fderiv ℝ (Function.uncurry f) (x, z)).comp
      (ContinuousLinearMap.inr ℝ A P)) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (x, z) :=
    (hf.differentiableOn (lt_of_lt_of_le zero_lt_one hm).ne').differentiableAt
      ((hU.prod hV).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)

lemma contDiffOn_partial {A P : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set A} {V : Set P} {f : A → P → E} {m n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hnm : n + 1 ≤ m)
    (hU : IsOpen U) (hV : IsOpen V) :
    ContDiffOn ℝ n (Function.uncurry fun x z => fderiv ℝ (f x) z) (U ×ˢ V) := by
  have h1 : ContDiffOn ℝ n (fun p : A × P => (fderiv ℝ (Function.uncurry f) p).comp
      (ContinuousLinearMap.inr ℝ A P)) (U ×ˢ V) :=
    (hf.fderiv_of_isOpen (hU.prod hV) hnm).clm_comp contDiffOn_const
  refine h1.congr ?_
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  exact (hasFDerivAt_partial hf (le_trans le_add_self hnm) hU hV hx hz).fderiv

/-- Differentiation under the integral sign, with domination from compactness. -/
theorem hasFDerivAt_integral_on_compact {A P : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [MeasurableSpace A] [OpensMeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ] {K U : Set A} {V : Set P}
    {f : A → P → E} {m : WithTop ℕ∞}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hm : 1 ≤ m)
    {y : P} (hy : y ∈ V) :
    HasFDerivAt (fun z => ∫ x, f x z ∂μ) (∫ x, fderiv ℝ (f x) y ∂μ) y := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV y hy
  have hsV : Metric.closedBall y (r / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrV
  have hs : Metric.closedBall y (r / 2) ∈ 𝓝 y := Metric.closedBall_mem_nhds y (by linarith)
  have hcont1 : ContinuousOn (Function.uncurry fun x z => fderiv ℝ (f x) z) (U ×ˢ V) :=
    (contDiffOn_partial hf (n := 0) (by simpa using hm) hU hV).continuousOn
  have hcont0 : ContinuousOn (Function.uncurry f) (U ×ˢ V) := hf.continuousOn
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall y (r / 2))).exists_bound_of_continuousOn
    (hcont1.mono (Set.prod_mono hKU hsV))
  have hKae := ae_mem_of_measure_compl hμ
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z x => f x z)
    (F' := fun z x => fderiv ℝ (f x) z) (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs] with z hz
    exact (integrable_of_continuousOn hK hμ
      (continuousOn_slice hcont0 hKU (hsV hz))).aestronglyMeasurable
  · exact integrable_of_continuousOn hK hμ (continuousOn_slice hcont0 hKU hy)
  · exact (integrable_of_continuousOn hK hμ
      (continuousOn_slice hcont1 hKU hy)).aestronglyMeasurable
  · filter_upwards [hKae] with x hx z hz
    exact hC (x, z) ⟨hx, hz⟩
  · exact integrable_const C
  · filter_upwards [hKae] with x hx z hz
    exact (hasFDerivAt_partial hf hm hU hV (hKU hx) (hsV hz)).differentiableAt.hasFDerivAt

/-- A fixed compactly carried finite-measure integral of a jointly `C^(k+1)` kernel is
`C^k` in the parameter, proved by iterating differentiation under the integral sign. -/
theorem contDiffOn_integral_on_compact {A P : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [OpensMeasurableSpace A]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    {μ : Measure A} [IsFiniteMeasure μ] {K U : Set A} {V : Set P}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    (k : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : A → P → E),
      ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) (U ×ˢ V) →
      ContDiffOn ℝ (k : WithTop ℕ∞) (fun z => ∫ x, f x z ∂μ) V := by
  induction k with
  | zero =>
    intro E _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    intro y hy
    exact (hasFDerivAt_integral_on_compact hK hKU hU hV hμ hf (by simp) hy).continuousAt.continuousWithinAt
  | succ k ih =>
    intro E _ _ f hf
    have h1 : (1 : WithTop ℕ∞) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) :=
      le_trans (by simp) (Nat.cast_le.2 (by omega : 1 ≤ k + 1 + 1))
    have hf' := contDiffOn_partial hf (n := ((k + 1 : ℕ) : WithTop ℕ∞))
      (Nat.cast_succ (k + 1)).ge hU hV
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hV]
    refine ⟨fun y hy =>
      (hasFDerivAt_integral_on_compact hK hKU hU hV hμ hf h1 hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine (ih _ hf').congr fun y hy => ?_
    exact (hasFDerivAt_integral_on_compact hK hKU hU hV hμ hf h1 hy).fderiv


@[expose] def parameterSecondOrder (a : (I dim) → (I dim) → ℝ) (b : (I dim) → ℝ) (c : ℝ)
    (f : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  (∑ i, ∑ j, a i j * fderiv ℝ (fun z => fderiv ℝ f z (axis j)) y (axis i)) +
    (∑ i, b i * fderiv ℝ f y (axis i)) + c*f y

theorem integral_parameterSecondOrder {μ : Measure (X dim)} [IsFiniteMeasure μ] {K U V : Set (X dim)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    {H : (X dim) → (X dim) → ℝ} (hH : ContDiffOn ℝ 2 (Function.uncurry H) (U ×ˢ V))
    (a : (I dim) → (I dim) → ℝ) (b : (I dim) → ℝ) (c : ℝ) {y : (X dim)} (hy : y ∈ V) :
    parameterSecondOrder a b c (fun z => ∫ x, H x z ∂μ) y =
      ∫ x, parameterSecondOrder a b c (H x) y ∂μ := by
  have hH1 : ContDiffOn ℝ 1 (Function.uncurry fun x z => fderiv ℝ (H x) z) (U ×ˢ V) :=
    contDiffOn_partial hH (by norm_num) hU hV
  have hG : ∀ j, ContDiffOn ℝ 1
      (Function.uncurry fun x z => fderiv ℝ (H x) z (axis j)) (U ×ˢ V) :=
    fun j => hH1.clm_apply contDiffOn_const
  have hG0 : ∀ j, ContinuousOn (Function.uncurry fun x z =>
      fderiv ℝ (fun w => fderiv ℝ (H x) w (axis j)) z) (U ×ˢ V) :=
    fun j => (contDiffOn_partial (hG j) (n := 0) (by norm_num) hU hV).continuousOn
  have i0 : Integrable (fun x => H x y) μ :=
    integrable_of_continuousOn hK hμ (continuousOn_slice hH.continuousOn hKU hy)
  have i1 : ∀ z ∈ V, Integrable (fun x => fderiv ℝ (H x) z) μ := fun z hz =>
    integrable_of_continuousOn hK hμ (continuousOn_slice hH1.continuousOn hKU hz)
  have i1' : ∀ i, Integrable (fun x => fderiv ℝ (H x) y (axis i)) μ := fun i =>
    integrable_of_continuousOn hK hμ
      ((continuousOn_slice hH1.continuousOn hKU hy).clm_apply continuousOn_const)
  have i2 : ∀ j, Integrable
      (fun x => fderiv ℝ (fun w => fderiv ℝ (H x) w (axis j)) y) μ := fun j =>
    integrable_of_continuousOn hK hμ (continuousOn_slice (hG0 j) hKU hy)
  have i2' : ∀ i j, Integrable (fun x => fderiv ℝ
      (fun w => fderiv ℝ (H x) w (axis j)) y (axis i)) μ :=
    fun i j => integrable_of_continuousOn hK hμ
      ((continuousOn_slice (hG0 j) hKU hy).clm_apply continuousOn_const)
  have d1 : ∀ z ∈ V, ∀ v, fderiv ℝ (fun w => ∫ x, H x w ∂μ) z v =
      ∫ x, fderiv ℝ (H x) z v ∂μ := by
    intro z hz v
    rw [(hasFDerivAt_integral_on_compact hK hKU hU hV hμ hH (by norm_num) hz).fderiv,
      ContinuousLinearMap.integral_apply (i1 z hz)]
  have d2 : ∀ i j, fderiv ℝ (fun z => fderiv ℝ (fun w => ∫ x, H x w ∂μ) z (axis j))
      y (axis i) =
      ∫ x, fderiv ℝ (fun z => fderiv ℝ (H x) z (axis j)) y (axis i) ∂μ := by
    intro i j
    have heq : (fun z => fderiv ℝ (fun w => ∫ x, H x w ∂μ) z (axis j)) =ᶠ[𝓝 y]
        fun z => ∫ x, fderiv ℝ (H x) z (axis j) ∂μ := by
      filter_upwards [hV.mem_nhds hy] with z hz using d1 z hz (axis j)
    rw [heq.fderiv_eq, (hasFDerivAt_integral_on_compact hK hKU hU hV hμ (hG j) le_rfl hy).fderiv,
      ContinuousLinearMap.integral_apply (i2 j)]
  have hA : Integrable (fun x => ∑ i, ∑ j, a i j *
      fderiv ℝ (fun z => fderiv ℝ (H x) z (axis j)) y (axis i)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (i2' i j).const_mul _
  have hB : Integrable (fun x => ∑ i, b i * fderiv ℝ (H x) y (axis i)) μ :=
    integrable_finsetSum _ fun i _ => (i1' i).const_mul _
  have hAB : Integrable (fun x => (∑ i, ∑ j, a i j *
      fderiv ℝ (fun z => fderiv ℝ (H x) z (axis j)) y (axis i)) +
      ∑ i, b i * fderiv ℝ (H x) y (axis i)) μ := hA.add hB
  unfold parameterSecondOrder
  simp_rw [d2, d1 y hy]
  rw [integral_add hAB (i0.const_mul _), integral_add hA hB, integral_const_mul]
  congr 2
  · refine Eq.symm ((integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (i2' i j).const_mul (a i j)).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (integral_finsetSum _ fun j _ => (i2' i j).const_mul (a i j)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  · refine Eq.symm ((integral_finsetSum _ fun i _ => (i1' i).const_mul (b i)).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _


private theorem laplace_eq_parameterSecondOrder (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) :
    laplace g f y = parameterSecondOrder (fun i j => (g y)⁻¹ i j)
      (fun k => -(∑ i, ∑ j, (g y)⁻¹ i j * christoffel g y k i j)) 0 f y := by
  have h₂ (i j : (I dim)) : fderiv ℝ (fun z => fderiv ℝ f z (axis j)) y (axis i) =
      coordDeriv i (coordDeriv j f) y := rfl
  have h₁ (i : (I dim)) : fderiv ℝ f y (axis i) = coordDeriv i f y := rfl
  simp only [laplace, parameterSecondOrder, h₂, h₁, mul_sub,
    Finset.sum_sub_distrib, zero_mul, add_zero, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
  let a (i j k : I dim) := (g y)⁻¹ i j * (christoffel g y k i j * coordDeriv k f y)
  change (∑ i, ∑ j, ∑ k, a i j k) = ∑ k, ∑ i, ∑ j, a i j k
  calc
    _ = ∑ i, ∑ k, ∑ j, a i j k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- A fixed volume or surface integral of a jointly smooth kernel is
harmonic in the parameter when each slice on the compact carrier is. -/
theorem harmonic_integral_on_compact {μ : Measure (X dim)} [IsFiniteMeasure μ] {K U V : Set (X dim)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    {H : (X dim) → (X dim) → ℝ} (hH : ContDiffOn ℝ ∞ (Function.uncurry H) (U ×ˢ V))
    {g : (MetricField dim)} (hEq : ∀ x ∈ K, ∀ y ∈ V, laplace g (H x) y = 0) :
    Harmonic V g (fun y => ∫ x, H x y ∂μ) := by
  refine ⟨contDiffOn_infty.mpr (fun n => contDiffOn_integral_on_compact hK hKU hU hV hμ n _
    (hH.of_le (by simp))),?_⟩
  intro y hy
  rw [laplace_eq_parameterSecondOrder,
    integral_parameterSecondOrder hK hKU hU hV hμ (hH.of_le (by simp)) _ _ _ hy]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [ae_mem_of_measure_compl hμ] with x hx
  rw [← laplace_eq_parameterSecondOrder,hEq x hx y hy]

end CalderonN
