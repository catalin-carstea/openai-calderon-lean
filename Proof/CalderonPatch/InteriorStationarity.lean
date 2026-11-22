module

public import Proof.CalderonPatch.ChartEnergyIntegral

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis chartVolume chartVolume_mul_laplace_eq_divergence coordDeriv divergenceFlux laplace)

variable {n : ℕ}

private theorem integrable_mul_of_compactSupport {U : Set (X n)}
    {f g : X n → ℝ} (hf : Continuous f) (hg : ContinuousOn g U)
    (hC : HasCompactSupport f) (hU : tsupport f ⊆ U) :
    Integrable (fun x => f x * g x) := by
  have hi : IntegrableOn (fun x => f x * g x) (tsupport f) (volume : Measure (X n)) :=
    (hf.continuousOn.mul (hg.mono hU)).integrableOn_compact hC
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

/-- The ordinary coordinate Green pairing against a compact interior
test has zero integral. -/
theorem integral_coordinateGreenPairing_eq_zero
    {U : Set (X n)} (hU : IsOpen U) {γ : MetricField n} (hγ : CalderonN.SmoothMetric U γ)
    {a b : X n → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiff ℝ ∞ b)
    (hC : HasCompactSupport b) (hS : tsupport b ⊆ U) :
    (∫ x, b x * (chartVolume γ x * laplace γ a x) +
      ∑ i : I n, coordDeriv i b x * divergenceFlux γ a x i) = 0 := by
  let F (i : I n) (x : X n) := divergenceFlux γ a x i
  have hF (i : I n) := CalderonN.contDiffOn_divergenceFlux hU hγ ha i
  have hFb (i : I n) : Integrable (fun x => coordDeriv i b x * F i x) :=
    integrable_mul_of_compactSupport ((hb.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      (hF i).continuousOn (hC.fderiv_apply ℝ (axis i)) ((tsupport_fderiv_apply_subset ℝ (axis i)).trans hS)
  have hDF (i : I n) : Integrable (fun x => b x * coordDeriv i (F i) x) :=
    integrable_mul_of_compactSupport hb.continuous
      (CalderonN.contDiffOn_coordDeriv (hF i) hU i).continuousOn hC hS
  have hParts (i : I n) :
      (∫ x, b x * coordDeriv i (F i) x + coordDeriv i b x * F i x) = 0 := by
    have he := CalderonN.integral_mul_coordDeriv_eq_neg hU (hF i) hb hC hS i
    have he' : (∫ x, coordDeriv i b x * F i x) = -∫ x, coordDeriv i (F i) x * b x :=
      (integral_congr_ae (Eventually.of_forall fun x => mul_comm (coordDeriv i b x) (F i x))).trans he
    rw [integral_add (hDF i) (hFb i)]
    calc
      _ = (∫ x, b x * coordDeriv i (F i) x) + (-∫ x, b x * coordDeriv i (F i) x) := by
        congr 1
        exact he'.trans (congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)))
      _ = 0 := add_neg_cancel _
  have hD (x : X n) :
      b x * (chartVolume γ x * laplace γ a x) + ∑ i : I n, coordDeriv i b x * divergenceFlux γ a x i =
        ∑ i : I n, (b x * coordDeriv i (F i) x + coordDeriv i b x * F i x) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases hx : x ∈ U
    · rw [chartVolume_mul_laplace_eq_divergence hU hγ ha hx]
    · have hz : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hS h))
      simp only [hz,zero_mul,zero_add,F]
  calc
    _ = ∫ x, ∑ i : I n, (b x * coordDeriv i (F i) x + coordDeriv i b x * F i x) :=
      integral_congr_ae (Eventually.of_forall hD)
    _ = ∑ i : I n, ∫ x, b x * coordDeriv i (F i) x + coordDeriv i b x * F i x :=
      integral_finsetSum _ (fun i _ => (hDF i).add (hFb i))
    _ = 0 := Finset.sum_eq_zero (fun i _ => hParts i)

variable [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

omit [T2Space M] in
/-- A smooth test with compact support in an interior chart gives a
globally smooth compactly supported coordinate test by zero extension. -/
theorem exists_coordinate_test_of_supported_native_test (e : OpenPartialHomeomorph M (X n))
    (hes : ContMDiffOn K J ∞ e.symm e.target) {v : M → ℝ} (hv : ContMDiff J R ∞ v)
    (hC : HasCompactSupport v) (hS : tsupport v ⊆ e.source) :
    ∃ b : X n → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ e.target ∧
      EqOn (v ∘ e.symm) b e.target := by
  let b := e.target.indicator (v ∘ e.symm)
  let A := e '' tsupport v
  have hA : IsCompact A := hC.image_of_continuousOn (e.continuousOn.mono hS)
  have hAT : A ⊆ e.target := by
    rintro _ ⟨p,hp,rfl⟩
    exact e.map_source (hS hp)
  have hbA : tsupport b ⊆ A := by
    apply closure_minimal _ hA.isClosed
    intro x hx
    have hT : x ∈ e.target := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    have hV : v (e.symm x) ≠ 0 := by
      change e.target.indicator (v ∘ e.symm) x ≠ 0 at hx
      rwa [indicator_of_mem hT] at hx
    exact ⟨e.symm x,subset_tsupport _ hV,e.right_inv hT⟩
  refine ⟨b,?_,hA.of_isClosed_subset (isClosed_tsupport b) hbA,hbA.trans hAT,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.target
    · have hvS := (hv.comp_contMDiffOn hes).contDiffOn
      apply (hvS.contDiffAt (e.open_target.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    · have hzero := notMem_tsupport_iff_eventuallyEq.mp (show x ∉ tsupport b from fun h => hx (hAT (hbA h)))
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hzero
  · intro x hx
    exact (indicator_of_mem hx _).symm

variable [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] in
/-- The native Green pairing against a smooth test compactly supported
inside an interior chart has zero integral. -/
theorem integral_nativeGreenPairing_interior_support_eq_zero (g : SmoothMetric n M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (hC : HasCompactSupport v) (hS : tsupport v ⊆ e.source) :
    (∫ p, v p * nativeLaplace g u p + energyPairingDensity g u v p ∂μ) = 0 := by
  obtain ⟨b,hb,hbC,hbS,hB⟩ := exists_coordinate_test_of_supported_native_test e hes hv hC hS
  let γ := coordinateMetric g e
  let a := u ∘ e.symm
  let f (x : X n) := b x * (chartVolume γ x * laplace γ a x) +
    ∑ i : I n, coordDeriv i b x * divergenceFlux γ a x i
  have hγ := coordinateMetric_smooth g e he hes
  have ha : ContDiffOn ℝ ∞ a e.target := (hu.comp_contMDiffOn hes).contDiffOn
  calc
    _ = ∫ p in e.source, v p * nativeLaplace g u p + energyPairingDensity g u v p ∂μ := by
      rw [← integral_indicator e.open_source.measurableSet]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ e.source
      · rw [indicator_of_mem hx]
      · have hNot : x ∉ tsupport v := fun h => hx (hS h)
        rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport hNot,zero_mul,
          energyPairingDensity_eq_zero_off_tsupport g u v hNot,zero_add]
    _ = ∫ x in e.target, f x :=
      integral_nativeGreenPairing_in_coordinates g μ hμ e heI he hes hu.contMDiffOn
        hv.contMDiffOn (fun _ _ => rfl) (fun _ _ => rfl) hB
    _ = ∫ x, f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hNot : x ∉ tsupport b := fun h => hx (hbS h)
      have hz (i : I n) : coordDeriv i b x = 0 := by
        unfold coordDeriv
        rw [fderiv_of_notMem_tsupport ℝ hNot,zero_apply]
      simp [f, image_eq_zero_of_notMem_tsupport hNot,hz]
    _ = 0 := integral_coordinateGreenPairing_eq_zero e.open_target hγ ha hb hbC hbS

end CalderonPatch
