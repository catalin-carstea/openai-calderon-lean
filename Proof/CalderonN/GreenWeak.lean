module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring

public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {n : ℕ}

private theorem contDiff_coordDeriv {u : (X n) → ℝ} (hu : ContDiff ℝ ∞ u) (j : (I n)) :
    ContDiff ℝ ∞ (coordDeriv j u) :=
  (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem tsupport_coordDeriv_subset (u : (X n) → ℝ) (i : (I n)) :
    tsupport (coordDeriv i u) ⊆ tsupport u := tsupport_fderiv_apply_subset ℝ (axis i)

private theorem contDiff_mul_local {U : Set (X n)} (hU : IsOpen U) {φ f : (X n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiffOn ℝ ∞ f U) (hsub : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun x => φ x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (hφ.contDiffOn.mul hf).contDiffAt (hU.mem_nhds hx)
  · have hclosed : IsClosed (tsupport φ) := isClosed_closure
    have hn : (tsupport φ)ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (fun h => hx (hsub h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

private theorem integrable_mul_local {U : Set (X n)} (hU : IsOpen U) {φ f : (X n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiffOn ℝ ∞ f U) (hc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) :
    Integrable (fun x => φ x * f x) (volume : Measure (X n)) :=
  (contDiff_mul_local hU hφ hf hsub).continuous.integrable_of_hasCompactSupport
    (hc.mul_right)

theorem integral_mul_coordDeriv_eq_neg {U : Set (X n)} (hU : IsOpen U)
    {f φ : (X n) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (i : (I n)) :
    (∫ x, f x * coordDeriv i φ x) = -∫ x, coordDeriv i f x * φ x := by
  have hdf := contDiffOn_coordDeriv hf hU i
  have hdφ := contDiff_coordDeriv hφ i
  have hdφc := hφc.fderiv_apply ℝ (axis i)
  have hdφU := (tsupport_coordDeriv_subset φ i).trans hφU
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((integrable_mul_local hU hφ hdf hφc hφU).congr (Eventually.of_forall fun _ => mul_comm _ _))
    ((integrable_mul_local hU hdφ hf hdφc hdφU).congr (Eventually.of_forall fun _ => mul_comm _ _))
    ((integrable_mul_local hU hφ hf hφc hφU).congr (Eventually.of_forall fun _ => mul_comm _ _))
    (fun x hx => (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hφU hx)))
    (fun x _ => hφ.differentiable (by simp) x)

theorem tsupport_laplace_subset (g : (MetricField n)) (u : (X n) → ℝ) :
    tsupport (laplace g u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have h₁ (i : (I n)) : coordDeriv i u x = 0 := by
    unfold coordDeriv
    rw [fderiv_of_notMem_tsupport ℝ hn, zero_apply]
  have h₂ (i j : (I n)) : coordDeriv i (coordDeriv j u) x = 0 := by
    change fderiv ℝ (coordDeriv j u) x (axis i) = 0
    rw [fderiv_of_notMem_tsupport ℝ (fun hy => hn (tsupport_coordDeriv_subset u j hy)),
      zero_apply]
  exact hx (by simp only [laplace, h₁, h₂, mul_zero, Finset.sum_const_zero, sub_zero])

private theorem flux_test {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)} (hg : SmoothMetric U g)
    {φ : (X n) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (i : (I n)) :
    ContDiff ℝ ∞ (fun x => divergenceFlux g φ x i) ∧
      HasCompactSupport (fun x => divergenceFlux g φ x i) ∧
      tsupport (fun x => divergenceFlux g φ x i) ⊆ tsupport φ := by
  have hs : tsupport (fun x => divergenceFlux g φ x i) ⊆ tsupport φ := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    apply hx
    have hz (j : (I n)) : coordDeriv j φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx => hn (tsupport_coordDeriv_subset φ j hx))
    simp only [divergenceFlux, hz, mul_zero, Finset.sum_const_zero]
  refine ⟨?_, hφc.of_isClosed_subset isClosed_closure hs, hs⟩
  apply ContDiff.sum
  intro j _
  have h := contDiff_mul_local hU (contDiff_coordDeriv hφ j)
    (contDiffOn_divergenceCoeff hg i j) ((tsupport_coordDeriv_subset φ j).trans hφU)
  convert h using 1
  funext x
  exact mul_comm _ _

theorem density_times_laplace_of_compact_test
    {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)} (hg : SmoothMetric U g)
    {φ : (X n) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun x => chartVolume g x * laplace g φ x) ∧
      HasCompactSupport (fun x => chartVolume g x * laplace g φ x) ∧
      tsupport (fun x => chartVolume g x * laplace g φ x) ⊆ tsupport φ := by
  have hs : tsupport (fun x => chartVolume g x * laplace g φ x) ⊆ tsupport φ :=
    tsupport_mul_subset_right.trans (tsupport_laplace_subset g φ)
  refine ⟨?_, hφc.of_isClosed_subset isClosed_closure hs, hs⟩
  let F (i : (I n)) (x : (X n)) := divergenceFlux g φ x i
  have hF (i : (I n)) := flux_test hU hg hφ hφc hφU i
  have he : (fun x => chartVolume g x * laplace g φ x) = fun x => ∑ i, coordDeriv i (F i) x := by
    funext x
    by_cases hx : x ∈ U
    · exact chartVolume_mul_laplace_eq_divergence hU hg hφ.contDiffOn hx
    · have hz : laplace g φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx (hφU (tsupport_laplace_subset g φ h)))
      have hd (i : (I n)) : coordDeriv i (F i) x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx (hφU ((hF i).2.2 (tsupport_coordDeriv_subset (F i) i h))))
      simp only [hz, hd, mul_zero, Finset.sum_const_zero]
  rw [he]
  exact ContDiff.sum fun i _ => contDiff_coordDeriv (hF i).1 i

/-- The coordinate Laplace--Beltrami operator is symmetric against a
test supported in the chart, with the exact volume density. -/
theorem integral_laplace_symmetric_of_compact_test
    {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)} (hg : SmoothMetric U g)
    {f φ : (X n) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ x, f x * laplace g φ x * chartVolume g x) =
      ∫ x, φ x * (chartVolume g x * laplace g f x) := by
  let F (i : (I n)) (x : (X n)) := divergenceFlux g f x i
  let P (i : (I n)) (x : (X n)) := divergenceFlux g φ x i
  have hP (i : (I n)) := flux_test hU hg hφ hφc hφU i
  have hPU (i : (I n)) : tsupport (P i) ⊆ U := (hP i).2.2.trans hφU
  have hDP (i : (I n)) : ContDiff ℝ ∞ (coordDeriv i (P i)) := contDiff_coordDeriv (hP i).1 i
  have hFU (i : (I n)) : ContDiffOn ℝ ∞ (F i) U := contDiffOn_divergenceFlux hU hg hf i
  have hDPinter (i : (I n)) : Integrable (fun x => f x * coordDeriv i (P i) x) := by
    exact (integrable_mul_local hU (hDP i) hf ((hP i).2.1.fderiv_apply ℝ (axis i))
      ((tsupport_coordDeriv_subset (P i) i).trans (hPU i))).congr
      (Eventually.of_forall fun _ => mul_comm _ _)
  have hDFinter (i : (I n)) : Integrable (fun x => φ x * coordDeriv i (F i) x) :=
    integrable_mul_local hU hφ (contDiffOn_coordDeriv (hFU i) hU i) hφc hφU
  have hFinter (i : (I n)) : Integrable (fun x => F i x * coordDeriv i φ x) :=
    (integrable_mul_local hU (contDiff_coordDeriv hφ i) (hFU i) (hφc.fderiv_apply ℝ (axis i))
      ((tsupport_coordDeriv_subset φ i).trans hφU)).congr (Eventually.of_forall fun _ => mul_comm _ _)
  have hPinter (i : (I n)) : Integrable (fun x => coordDeriv i f x * P i x) :=
    (integrable_mul_local hU (hP i).1 (contDiffOn_coordDeriv hf hU i) (hP i).2.1 (hPU i)).congr
      (Eventually.of_forall fun _ => mul_comm _ _)
  have hflux (x : (X n)) :
      (∑ i, coordDeriv i f x * P i x) = ∑ i, F i x * coordDeriv i φ x := by
    by_cases hx : x ∈ U
    · simp only [P, F, divergenceFlux, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [divergenceCoeff_symm hg hx j i]
        ring
    · have hz (i : (I n)) : coordDeriv i φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hi =>
          hx (hφU (tsupport_coordDeriv_subset φ i hi)))
      simp only [P, divergenceFlux, hz, mul_zero, Finset.sum_const_zero]
  calc
    (∫ x, f x * laplace g φ x * chartVolume g x) =
        ∫ x, ∑ i, f x * coordDeriv i (P i) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change f x * laplace g φ x * chartVolume g x =
          ∑ i, f x * coordDeriv i (P i) x
        by_cases hx : x ∈ U
        · rw [← Finset.mul_sum, ← chartVolume_mul_laplace_eq_divergence hU hg hφ.contDiffOn hx]
          ring
        · have hz : laplace g φ x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hx (hφU (tsupport_laplace_subset g φ h)))
          have hzero (i : (I n)) : coordDeriv i (P i) x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hx (hPU i (tsupport_coordDeriv_subset (P i) i h)))
          simp only [hz, hzero, mul_zero, zero_mul, Finset.sum_const_zero]
    _ = -∫ x, ∑ i, coordDeriv i f x * P i x := by
      rw [integral_finsetSum Finset.univ (fun i _ => hDPinter i),
        integral_finsetSum Finset.univ (fun i _ => hPinter i), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        integral_mul_coordDeriv_eq_neg hU hf (hP i).1 (hP i).2.1 (hPU i) i
    _ = -∫ x, ∑ i, F i x * coordDeriv i φ x :=
      congrArg Neg.neg (integral_congr_ae (Eventually.of_forall hflux))
    _ = ∫ x, ∑ i, φ x * coordDeriv i (F i) x := by
      rw [integral_finsetSum Finset.univ (fun i _ => hFinter i),
        integral_finsetSum Finset.univ (fun i _ => hDFinter i), ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_coordDeriv_eq_neg hU (hFU i) hφ hφc hφU, neg_neg]
      exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∑ i, φ x * coordDeriv i (F i) x) = φ x * (chartVolume g x * laplace g f x)
        rw [← Finset.mul_sum]
        by_cases hx : x ∈ U
        · rw [← chartVolume_mul_laplace_eq_divergence hU hg hf hx]
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h)), zero_mul, zero_mul]

theorem isOpen_offDiagonal {Ω : Set (X n)} (hΩ : IsOpen Ω) : IsOpen (OffDiagonal Ω) := by
  have he : OffDiagonal Ω = Ω ×ˢ Ω ∩ {q : (X n) × (X n) | q.1 ≠ q.2} := by
    ext q
    simp only [OffDiagonal, mem_ofPred_eq, mem_inter_iff, mem_prod, and_assoc]
  rw [he]
  exact (hΩ.prod hΩ).inter (isOpen_ne_fun continuous_fst continuous_snd)

/-- The distributional Green law gives the classical homogeneous equation
off the pole. Smoothness there is part of the chart Green germ. -/
theorem GreenGerm.harmonic_left {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)}
    (hg : SmoothMetric Ω g) {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G) {y : (X n)} (hy : y ∈ Ω) :
    Harmonic (Ω \ {y}) g (fun x => G (x, y)) := by
  let U := Ω \ {y}
  let f (x : (X n)) := G (x, y)
  let D (x : (X n)) := chartVolume g x * laplace g f x
  have hU : IsOpen U := hΩ.sdiff isClosed_singleton
  have hUΩ : U ⊆ Ω := sdiff_subset
  have hgU : SmoothMetric U g := ⟨fun i j => (hg.1 i j).mono hUΩ, fun x hx => hg.2 x (hUΩ hx)⟩
  have hf : ContDiffOn ℝ ∞ f U :=
    hG.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => ⟨hx.1, hy, hx.2⟩)
  have hD : ContDiffOn ℝ ∞ D U := by
    have hs : ContDiffOn ℝ ∞ (fun x => ∑ i, coordDeriv i (fun z => divergenceFlux g f z i) x) U :=
      ContDiffOn.sum fun i _ => contDiffOn_coordDeriv (contDiffOn_divergenceFlux hU hgU hf i) hU i
    exact hs.congr fun x hx => chartVolume_mul_laplace_eq_divergence hU hgU hf hx
  have htests (φ : (X n) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφU : tsupport φ ⊆ U) :
        ∫ x, φ x • D x = 0 := by
    have hφΩ := hφU.trans hUΩ
    have hzero : φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (hφU h).2 (mem_singleton y))
    have htest := (hG.2.2 y hy).2 φ hφ hφc hφΩ
    rw [hzero, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : laplace g φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx (hφΩ (tsupport_laplace_subset g φ h)))
      simp only [hz, neg_zero, mul_zero, zero_mul])] at htest
    have hzero' : (∫ x, f x * laplace g φ x * chartVolume g x) = 0 := by
      change (∫ x, f x * (-laplace g φ x) * chartVolume g x) = 0 at htest
      simpa only [mul_neg, neg_mul, integral_neg, neg_eq_zero] using htest
    change (∫ x, φ x * D x) = 0
    exact (integral_laplace_symmetric_of_compact_test hU hgU hf hφ hφc hφU).symm.trans hzero'
  have hAE : D =ᵐ[(volume : Measure (X n)).restrict U] 0 :=
    (ae_restrict_iff' hU.measurableSet).mpr
      (hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hD.continuousOn.locallyIntegrableOn hU.measurableSet) htests)
  have he : EqOn D 0 U := Measure.eqOn_open_of_ae_eq hAE hU hD.continuousOn continuousOn_const
  refine ⟨hf, fun x hx => ?_⟩
  have hz : D x = 0 := he hx
  exact (mul_eq_zero.mp hz).resolve_left (Real.sqrt_pos.2 (hgU.2 x hx).det_pos).ne'

theorem laplace_congrOn {U : Set (X n)} (hU : IsOpen U) {g h : (MetricField n)} (hgh : EqOn g h U)
    {f k : (X n) → ℝ} (hfk : EqOn f k U) {x : (X n)} (hx : x ∈ U) :
    laplace g f x = laplace h k x := by
  have hder (a b c : (I n)) : coordDeriv a (fun y => g y b c) x =
      coordDeriv a (fun y => h y b c) x :=
    eqOn_coordDeriv hU (fun y hy => congrArg (fun M : (Mat n) => M b c) (hgh hy)) a hx
  have hΓ (a b c : (I n)) : christoffel g x a b c = christoffel h x a b c := by
    simp only [christoffel, hgh hx, hder]
  have hd (i : (I n)) : coordDeriv i f x = coordDeriv i k x := eqOn_coordDeriv hU hfk i hx
  have hdd (i j : (I n)) : coordDeriv i (coordDeriv j f) x = coordDeriv i (coordDeriv j k) x :=
    eqOn_coordDeriv hU (eqOn_coordDeriv hU hfk j) i hx
  simp only [laplace, hgh hx, hΓ, hd, hdd]

theorem GreenGerm.harmonic_right {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)}
    (hg : SmoothMetric Ω g) {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G) {x : (X n)} (hx : x ∈ Ω) :
    Harmonic (Ω \ {x}) g (fun y => G (x, y)) := by
  have hU : IsOpen (Ω \ {x}) := hΩ.sdiff isClosed_singleton
  have he : EqOn (fun y => G (x, y)) (fun y => G (y, x)) (Ω \ {x}) := fun y hy =>
    hG.2.1 _ ⟨hx, hy.1, fun h => hy.2 (mem_singleton_iff.mpr h.symm)⟩
  have hL := hG.harmonic_left hΩ hg hx
  exact ⟨hL.1.congr he, fun y hy =>
    (laplace_congrOn hU (fun _ _ => rfl) he hy).trans (hL.2 y hy)⟩

end CalderonN
