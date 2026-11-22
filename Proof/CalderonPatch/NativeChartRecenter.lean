module

public import Proof.CalderonPatch.ChartDensity
public import Proof.CalderonPatch.ChartTranslation

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- Recenter an existing chart at an arbitrary point of its target. -/
@[expose] def recenterChart (e : OpenPartialHomeomorph M (X n)) (c : X n) :
    OpenPartialHomeomorph M (X n) :=
  e.trans (Homeomorph.addLeft c).symm.toOpenPartialHomeomorph

@[simp]
theorem recenterChart_source (e : OpenPartialHomeomorph M (X n)) (c : X n) :
    (recenterChart e c).source = e.source := by
  change e.source ∩ (e : M → X n) ⁻¹' univ = e.source
  rw [preimage_univ, inter_univ]

theorem recenterChart_target (e : OpenPartialHomeomorph M (X n)) (c : X n) :
    (recenterChart e c).target = (c + ·) ⁻¹' e.target := by
  change univ ∩ (c + ·) ⁻¹' e.target = _
  rw [univ_inter]

@[simp]
theorem recenterChart_symm_apply (e : OpenPartialHomeomorph M (X n)) (c y : X n) :
    (recenterChart e c).symm y = e.symm (c+y) := rfl

theorem recenterChart_zero_mem (e : OpenPartialHomeomorph M (X n)) {c : X n} (hc : c ∈ e.target) :
    (0 : X n) ∈ (recenterChart e c).target := by
  rw [recenterChart_target]
  change c+0 ∈ e.target
  rwa [add_zero]

variable [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "Y" => X n
local notation "P" => 𝓘(ℝ, X n)

variable (e : OpenPartialHomeomorph M (X n))
  (he : ContMDiffOn (𝓡∂ n) 𝓘(ℝ, X n) ∞ e e.source)
  (hes : ContMDiffOn 𝓘(ℝ, X n) (𝓡∂ n) ∞ e.symm e.target)

omit [IsManifold (𝓡∂ n) ∞ M] in
include he in
theorem recenterChart_smooth (c : Y) :
    ContMDiffOn J P ∞ (recenterChart e c) (recenterChart e c).source := by
  rw [recenterChart_source]
  have hT : ContMDiff P P ∞ (fun z : Y => -c+z) := (contDiff_const.add contDiff_id).contMDiff
  exact hT.comp_contMDiffOn he

omit [IsManifold (𝓡∂ n) ∞ M] in
include hes in
theorem recenterChart_smooth_inverse (c : Y) :
    ContMDiffOn P J ∞ (recenterChart e c).symm (recenterChart e c).target := by
  rw [recenterChart_target]
  have hT : ContMDiff P P ∞ (c + ·) := (contDiff_const.add contDiff_id).contMDiff
  exact hes.comp hT.contMDiffOn (fun _ h => h)

include hes in
/-- Translation leaves the basis of the coordinate metric unchanged. -/
theorem coordinateMetric_recenter (g : SmoothMetric n M) (c : Y) :
    EqOn (coordinateMetric g (recenterChart e c)) (fun y => coordinateMetric g e (c+y))
      (recenterChart e c).target := by
  intro y hy
  have hy' : c+y ∈ e.target := by
    rw [recenterChart_target] at hy
    exact hy
  have hS := (hes.contMDiffAt (e.open_target.mem_nhds hy')).mdifferentiableAt (by simp)
  have hT : ContMDiff P P ∞ (c + ·) := (contDiff_const.add contDiff_id).contMDiff
  have hDiff : mfderiv P J (recenterChart e c).symm y = mfderiv P J e.symm (c+y) := by
    rw [show ((recenterChart e c).symm : Y → M) = e.symm ∘ (c + ·) from rfl,
      mfderiv_comp y hS (hT.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, fderiv_const_add,
      fderiv_fun_id]
    ext v
    rfl
  ext i j
  change g.inner ((recenterChart e c).symm y)
    (mfderiv P J (recenterChart e c).symm y (CalderonN.axis i))
    (mfderiv P J (recenterChart e c).symm y (CalderonN.axis j)) =
      g.inner (e.symm (c+y)) (mfderiv P J e.symm (c+y) (CalderonN.axis i))
        (mfderiv P J e.symm (c+y) (CalderonN.axis j))
  rw [hDiff,recenterChart_symm_apply]
  rfl

end CalderonPatch
