module

public import Proof.CalderonPatch.GreenInversePairing

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

namespace DirichletData

variable (D : DirichletData m M) (h : NativeInverseRegularity D)

private def negTest (t : ℝ) : ℝ := -expNegInvGlue (-t)

private theorem negTest_smooth : ContDiff ℝ ∞ negTest :=
  (expNegInvGlue.contDiff.comp contDiff_id.neg).neg

private theorem negTest_monotone : Monotone negTest :=
  fun _ _ hxy => neg_le_neg (expNegInvGlue.monotone (neg_le_neg hxy))

private theorem negTest_nonpos (t : ℝ) : negTest t ≤ 0 :=
  neg_nonpos.mpr (expNegInvGlue.nonneg _)

private theorem negTest_neg {t : ℝ} (ht : t < 0) : negTest t < 0 :=
  neg_neg_of_pos (expNegInvGlue.pos_of_pos (neg_pos.mpr ht))

private theorem negTest_zero : negTest 0 = 0 := by simp [negTest]

private theorem energyPairingDensity_negTest {u : M → ℝ} (hu : ContMDiff J R ∞ u) (p : M) :
    energyPairingDensity D.metric u (negTest ∘ u) p =
      deriv negTest (u p) * energyPairingDensity D.metric u u p := by
  let A : TangentSpace J p →L[ℝ] ℝ := mfderiv J R u p
  let B : TangentSpace J p →L[ℝ] ℝ := mfderiv J R (negTest ∘ u) p
  have hd : B = deriv negTest (u p) • A := by
    change mfderiv J R (negTest ∘ u) p = _
    rw [mfderiv_comp p (negTest_smooth.contMDiff.mdifferentiableAt (by simp))
      (hu.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    ext v
    change fderiv ℝ negTest (u p) (A v) = deriv negTest (u p) * A v
    calc
      _ = fderiv ℝ negTest (u p) (A v • (1 : ℝ)) := by rw [smul_eq_mul,mul_one]
      _ = A v * deriv negTest (u p) := by rw [map_smul,smul_eq_mul,deriv]
      _ = _ := mul_comm _ _
  rw [energyPairingDensity_symm D.metric u (negTest ∘ u)]
  change D.metric.inner p (metricDual D.metric p B) (metricDual D.metric p A) =
    deriv negTest (u p) * D.metric.inner p (metricDual D.metric p A) (metricDual D.metric p A)
  rw [metricDual_spec,metricDual_spec,hd]
  rfl

private theorem smoothInverse_nonneg_of_pos (φ : Source) (hφ : ∀ p, 0 < φ p) :
    ∀ p, 0 ≤ D.smoothInverse h φ p := by
  intro p
  by_contra! hp
  let u := D.smoothInverse h φ
  let v := negTest ∘ u
  have hu := (D.smoothInverse_spec h φ).1
  have hv : ContMDiff J R ∞ v := negTest_smooth.contMDiff.comp hu
  have hV0 : EqOn v 0 ((J).boundary M) := fun x hx => by
    change negTest (D.smoothInverse h φ x) = 0
    rw [(D.smoothInverse_spec h φ).2.1 hx,Pi.zero_apply,negTest_zero]
  have hGreen := integral_energyPairingDensity_eq_neg_laplace D.metric D.volume
    D.metric_volume hu hv hV0
  have hI : ∀ᵐ x ∂D.volume, x ∈ (J).interior M := by
    rw [ae_iff]
    change D.volume ((J).interior M)ᶜ = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero D.metric D.volume D.metric_volume
  have hR : (∫ x, energyPairingDensity D.metric u v x ∂D.volume) =
      ∫ x, φ x * v x ∂D.volume := by
    refine hGreen.trans (integral_congr_ae ?_)
    filter_upwards [hI] with x hx
    have he := (D.smoothInverse_spec h φ).2.2.1 hx
    change (-nativeLaplace D.metric u x) = φ x at he
    rw [he]
  have hN : 0 ≤ ∫ x, energyPairingDensity D.metric u v x ∂D.volume := by
    apply integral_nonneg
    intro x
    rw [energyPairingDensity_negTest D hu]
    exact mul_nonneg (negTest_monotone.deriv_nonneg) (energyPairingDensity_nonneg D.metric u x)
  have hP : 0 < ∫ x, -(φ x * v x) ∂D.volume := by
    let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
    let : D.volume.IsOpenPosMeasure := ⟨fun U hU hUne =>
      (D.metric_volume.measure_pos_of_open_nonempty hU hUne).ne'⟩
    have hC : Continuous (fun x => -(φ x * v x)) :=
      ((show ContMDiff J R ∞ (φ : M → ℝ) from φ.property).continuous.mul hv.continuous).neg
    apply hC.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun x => neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hφ x).le (negTest_nonpos _)))
    exact (neg_pos.mpr (mul_neg_of_pos_of_neg (hφ p) (negTest_neg hp))).ne'
  rw [integral_neg,← hR] at hP
  linarith

/-- The smooth inverse preserves nonnegativity. A strict test can be
used after adding any positive constant to the source. -/
theorem smoothInverse_nonneg (φ : Source) (hφ : ∀ p, 0 ≤ φ p) (p : M) :
    0 ≤ D.smoothInverse h φ p := by
  let one : Source := ⟨fun _ => 1,contMDiff_const⟩
  let a := D.smoothInverse h φ p
  let b := D.smoothInverse h one p
  have hε : ∀ t : ℝ, 0 < t → 0 ≤ a + t*b := by
    intro t ht
    have hpos (x : M) : 0 < (φ + t • one : Source) x := by
      change 0 < φ x + t * 1
      rw [mul_one]
      exact add_pos_of_nonneg_of_pos (hφ x) ht
    have hh := D.smoothInverse_nonneg_of_pos h (φ + t • one) hpos p
    rw [← D.smoothInverseL_apply h, map_add, map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hh
    exact hh
  have hT : Tendsto (fun t : ℝ => a + t*b) (𝓝[Set.Ioi 0] 0) (𝓝 (a + 0*b)) :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.continuousWithinAt
  have hLim : 0 ≤ a + 0*b := ge_of_tendsto hT (eventually_mem_nhdsWithin.mono (fun t ht => hε t ht))
  simpa [a] using hLim

theorem smoothInverse_mono (φ ψ : Source) (hφ : ∀ p, φ p ≤ ψ p) (p : M) :
    D.smoothInverse h φ p ≤ D.smoothInverse h ψ p := by
  have hp := D.smoothInverse_nonneg h (ψ - φ) (fun x => sub_nonneg.mpr (hφ x)) p
  rw [← D.smoothInverseL_apply h, map_sub, Pi.sub_apply] at hp
  exact sub_nonneg.mp hp

end DirichletData

end CalderonPatch
