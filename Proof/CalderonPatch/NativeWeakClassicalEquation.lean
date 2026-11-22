module

public import Proof.CalderonPatch.DirichletWeakGreen

import Proof.CalderonPatch.InteriorChartBasis
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

omit [T2Space M] [CompactSpace M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
theorem contMDiff_mul_of_tsupport_subset {U : Set M} (hU : IsOpen U)
    {χ u : M → ℝ} (hχ : ContMDiff J R ∞ χ) (hχU : tsupport χ ⊆ U)
    (hu : ContMDiffOn J R ∞ u U) : ContMDiff J R ∞ (χ * u) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxU := hχU (tsupport_mul_subset_left hx)
  exact hχ.contMDiffAt.mul ((hu x hxU).contMDiffAt (hU.mem_nhds hxU))

/-- The completed weak Dirichlet equation agrees pointwise with
the classical equation on any open set where its value is smooth. -/
theorem nativeLaplace_eq_of_weakDirichletInverse_smooth_value
    (D : DirichletData m M) {U : Set M} (hU : IsOpen U)
    (f : Lp ℝ 2 D.volume) {q u : M → ℝ} (hq : ContMDiff J R ∞ q)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] q)
    (hu : ContMDiffOn J R ∞ u U)
    (hValue : (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict U] u) :
    EqOn (-nativeLaplace D.metric u) q (U ∩ (J).interior M) := by
  intro p hp
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  have hUI : IsOpen (U ∩ (J).interior M) := hU.inter ((J).isOpen_interior (n := ∞) (by simp))
  obtain ⟨χ,_,hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := J) p).mem_iff.1 (hUI.mem_nhds hp)
  let w : M → ℝ := χ * u
  have hw : ContMDiff J R ∞ w := contMDiff_mul_of_tsupport_subset hU χ.contMDiff (hχ.trans inter_subset_left) hu
  have hwB : EqOn w 0 ((J).boundary M) := by
    intro x hx
    have hN : x ∉ tsupport (χ : M → ℝ) := fun h => ((J).isInteriorPoint_iff_not_isBoundaryPoint x).1 (hχ h).2 hx
    change χ x * u x = 0
    rw [image_eq_zero_of_notMem_tsupport hN,zero_mul]
  let S := interior ((χ : M → ℝ) ⁻¹' {1}) ∩ (U ∩ (J).interior M)
  have hS : IsOpen S := isOpen_interior.inter hUI
  have hpS : p ∈ S := ⟨mem_interior_iff_mem_nhds.2 χ.eventuallyEq_one,hp⟩
  have hwU (x : M) (hx : x ∈ S) : w x = u x := by
    have h1 : χ x = 1 := mem_singleton_iff.1 (interior_subset hx.1 : x ∈ (χ : M → ℝ) ⁻¹' {1})
    simp [w,h1]
  obtain ⟨L,hL,hLΔ⟩ := exists_smooth_nativeLaplace D.metric hw
  let g : M → ℝ := -L - q
  have hg : ContMDiff J R ∞ g := hL.neg.sub hq
  obtain ⟨η,_,hη⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := J) p).mem_iff.1 (hS.mem_nhds hpS)
  let v : M → ℝ := η * g
  have hv : ContMDiff J R ∞ v := η.contMDiff.mul hg
  have hTS : tsupport v ⊆ S := tsupport_mul_subset_left.trans hη
  have hvB : EqOn v 0 ((J).boundary M) := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h =>
      ((J).isInteriorPoint_iff_not_isBoundaryPoint x).1 (hTS h).2.2 hx
  let φ := DirichletTest.ofSmooth (D := D) v hv hvB
  have hDiff : (∫ x, g x * v x ∂D.volume) = 0 := by
    have hWeak := D.weakDirichletInverse_distribution f φ
    have hAE₁ : (fun x => D.l2Value (D.weakDirichletInverse f) x * (-nativeLaplace D.metric v x))
        =ᵐ[D.volume] (fun x => w x * (-nativeLaplace D.metric v x)) := by
      filter_upwards [ae_imp_of_ae_restrict hValue] with x hx
      by_cases hxS : x ∈ S
      · rw [hx hxS.2.1,hwU x hxS]
      · have hZ : nativeLaplace D.metric v x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hxS (hTS (tsupport_nativeLaplace_subset D.metric v h))
        simp [hZ]
    have hAE₂ : (fun x => f x * v x) =ᵐ[D.volume] (fun x => q x * v x) := by
      filter_upwards [ae_imp_of_ae_restrict hf] with x hx
      by_cases hxS : x ∈ S
      · rw [hx hxS.2.1]
      · simp [image_eq_zero_of_notMem_tsupport (fun h => hxS (hTS h))]
    have hAE₃ : (fun x => (-nativeLaplace D.metric w x) * v x) =ᵐ[D.volume] (fun x => -L x * v x) :=
      Eventually.of_forall fun x => by
        change -nativeLaplace D.metric w x * v x = -L x * v x
        by_cases hxS : x ∈ S
        · rw [hLΔ hxS.2.2]
        · simp [image_eq_zero_of_notMem_tsupport (fun h => hxS (hTS h))]
    have hWeak' : (∫ x, w x * (-nativeLaplace D.metric v x) ∂D.volume) =
        ∫ x, q x * v x ∂D.volume := by
      rw [← integral_congr_ae hAE₁,← integral_congr_ae hAE₂]
      exact hWeak
    have hGreen : (∫ x, (-nativeLaplace D.metric w x) * v x ∂D.volume) =
        ∫ x, w x * (-nativeLaplace D.metric v x) ∂D.volume := by
      rw [← integral_energyPairingDensity_eq_neg_laplace D.metric D.volume
        D.metric_volume hw hv hvB]
      calc
        _ = ∫ x, energyPairingDensity D.metric v w x ∂D.volume :=
          integral_congr_ae (Eventually.of_forall (energyPairingDensity_symm D.metric w v))
        _ = ∫ x, (-nativeLaplace D.metric v x) * w x ∂D.volume :=
          integral_energyPairingDensity_eq_neg_laplace D.metric D.volume D.metric_volume hv hw hwB
        _ = _ := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have hEq : (∫ x, -L x * v x ∂D.volume) = ∫ x, q x * v x ∂D.volume :=
      (integral_congr_ae hAE₃).symm.trans (hGreen.trans hWeak')
    have hI₁ : Integrable (fun x => -L x * v x) D.volume :=
      (hL.continuous.neg.mul hv.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hI₂ : Integrable (fun x => q x * v x) D.volume :=
      (hq.continuous.mul hv.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simpa only [g,Pi.sub_apply,Pi.neg_apply,sub_mul,integral_sub hI₁ hI₂,sub_eq_zero] using hEq
  have hgP : g p = 0 := by
    by_contra hn
    let F : M → ℝ := g * v
    have hF : Continuous F := hg.continuous.mul hv.continuous
    have hF₀ : ∀ x, 0 ≤ F x := fun x => by
      change 0 ≤ g x * (η x * g x)
      rw [mul_left_comm,← pow_two]
      exact mul_nonneg η.nonneg (sq_nonneg _)
    have hFpos : 0 < F p := by
      change 0 < g p * (η p * g p)
      rw [η.eq_one,one_mul,← pow_two]
      exact sq_pos_of_ne_zero hn
    have hSupp : (Function.support F).Nonempty := ⟨p,hFpos.ne'⟩
    have hInt : Integrable F D.volume :=
      hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hPos := (integral_pos_iff_support_of_nonneg hF₀ hInt).2
      (D.metric_volume.measure_pos_of_open_nonempty hF.isOpen_support hSupp)
    exact hPos.ne' hDiff
  obtain ⟨e,hpE,heS,heI,he,hes⟩ := exists_interiorChart p hp.2 hS hpS
  have hEq : EqOn (w ∘ e.symm) (u ∘ e.symm) e.target :=
    fun z hz => hwU _ (heS (e.map_target hz))
  have hP : nativeLaplace D.metric w p = nativeLaplace D.metric u p := by
    rw [nativeLaplace_eq_coordinate D.metric e heI he hes hw.contMDiffOn hpE,
      nativeLaplace_eq_coordinate D.metric e heI he hes
        (hu.mono (heS.trans (fun _ hx => hx.2.1))) hpE,
      CalderonN.laplace_congrOn e.open_target (fun _ _ => rfl) hEq (e.map_source hpE)]
  change -nativeLaplace D.metric u p = q p
  rw [← hP,← hLΔ hp.2]
  exact sub_eq_zero.mp hgP

end CalderonPatch
