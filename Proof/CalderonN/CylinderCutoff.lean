module

public import Proof.CalderonN.ConformalDepth
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} {normal : I dim}
open FixedTube

@[expose] def coordinateCylinder (normal : I dim) : Set (X dim) :=
  {y | transversePair normal y y ≤ 1 ∧ -1 ≤ y normal ∧ y normal ≤ 1}

private theorem continuous_transversePair_self :
    Continuous (fun y : X dim => transversePair normal y y) := by
  unfold transversePair
  apply continuous_finsetSum
  intro i hi
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.mul (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

theorem isClosed_coordinateCylinder : IsClosed (coordinateCylinder normal) := by
  change IsClosed ({y : (X dim) | transversePair normal y y ≤ 1} ∩
    ({y : (X dim) | (-1 : ℝ) ≤ y normal} ∩ {y : (X dim) | y normal ≤ 1}))
  exact (isClosed_le (continuous_transversePair_self (normal := normal)) continuous_const).inter
    ((isClosed_le continuous_const (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const))

theorem coordinateCylinder_subset_closedBall : (coordinateCylinder normal) ⊆ closedBall (0 : (X dim)) 2 := by
  intro y hy
  have hsq : ‖y‖^2 = transversePair normal y y + (y normal)^2 := norm_sq_eq_transversePair normal y
  have h2 : (y normal)^2 ≤ 1 := by
    have h₁ : 0 ≤ y normal + 1 := by linarith [hy.2.1]
    have h₂ : 0 ≤ 1 - y normal := by linarith [hy.2.2]
    nlinarith [mul_nonneg h₁ h₂]
  exact mem_closedBall_zero_iff.mpr (by nlinarith [norm_nonneg y, hy.1])

theorem isCompact_coordinateCylinder : IsCompact (coordinateCylinder normal) :=
  (isCompact_closedBall (0 : (X dim)) 2).of_isClosed_subset (isClosed_coordinateCylinder (normal := normal))
    (coordinateCylinder_subset_closedBall (normal := normal))

theorem mem_coordinateCylinder_interior {y : (X dim)} (hh : transversePair normal y y < 1)
    (hlo : -1 < y normal) (hhi : y normal < 1) : y ∈ interior (coordinateCylinder normal) := by
  let V : Set (X dim) := {z | transversePair normal z z < 1} ∩
    ({z | (-1 : ℝ) < z normal} ∩ {z | z normal < 1})
  have hV : IsOpen V := (isOpen_lt (continuous_transversePair_self (normal := normal)) continuous_const).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const))
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds ⟨hh, hlo, hhi⟩)
    (fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩))

private def heightDepth (L t : ℝ) : ℝ := (Real.exp (-L / 4) - Real.exp (-2 * L * t)) / (2 * L)

private theorem heightDepth_strictMono {L : ℝ} (hL : 0 < L) : StrictMono (heightDepth L) := by
  intro a b hab
  unfold heightDepth
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * L)).mpr
  have h := Real.exp_lt_exp.mpr (show -2 * L * b < -2 * L * a by nlinarith)
  linarith

theorem exists_cylinderDepth_margin {L : ℝ} (hL : 0 < L) :
    ∃ tb : ℝ, 0 < tb ∧
      ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4 := by
  have hzero : heightDepth L (1/8) = 0 := by
    unfold heightDepth
    rw [show -2 * L * (1/8) = -L / 4 by ring, sub_self, zero_div]
  have hpos : 0 < heightDepth L (1/4) :=
    hzero ▸ heightDepth_strictMono hL (show (1/8 : ℝ) < 1/4 by norm_num)
  refine ⟨heightDepth L (1/4) / 4, by positivity, fun y hy => ?_⟩
  apply (heightDepth_strictMono hL).lt_iff_lt.mp
  change heightDepth L (parabolicHeight normal y) < heightDepth L (1/4)
  change heightDepth L (parabolicHeight normal y) ≤ 3 * (heightDepth L (1/4) / 4) at hy
  linarith

@[expose] def cylinderCore (normal : I dim) (L tb : ℝ) : Set (X dim) :=
  (coordinateCylinder normal) ∩ {y | -(1/2 : ℝ) ≤ y normal ∧ conformalDepth normal L y ≤ 2 * tb}

theorem isCompact_cylinderCore (L tb : ℝ) : IsCompact (cylinderCore normal L tb) := by
  change IsCompact ((coordinateCylinder normal) ∩ ({y : (X dim) | -(1/2 : ℝ) ≤ y normal} ∩
    {y | conformalDepth normal L y ≤ 2 * tb}))
  exact (isCompact_coordinateCylinder (normal := normal)).inter_right
    ((isClosed_le continuous_const ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).inter
      (isClosed_le ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const))

@[expose] def cylinderCutoff (normal : I dim) (L tb : ℝ) (y : (X dim)) : ℝ :=
  Real.smoothTransition ((y normal + 3/4) / (1/8)) *
    Real.smoothTransition ((3 * tb - conformalDepth normal L y) / (tb / 2))

theorem contDiff_cylinderCutoff (L tb : ℝ) : ContDiff ℝ ∞ (cylinderCutoff normal L tb) := by
  unfold cylinderCutoff
  have h : ContDiff ℝ ∞ (fun y : (X dim) => y normal) := (EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).contDiff
  refine (Real.smoothTransition.contDiff.comp ((h.add contDiff_const).div_const _)).mul ?_
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ((contDiff_conformalDepth (normal := normal)) L)).div_const _)

theorem cylinderCutoff_eq_one {L tb : ℝ} (htb : 0 < tb) {y : (X dim)}
    (hlo : -(5/8 : ℝ) ≤ y normal) (hhi : conformalDepth normal L y ≤ (5/2) * tb) :
    cylinderCutoff normal L tb y = 1 := by
  unfold cylinderCutoff
  have h₁ : (1 : ℝ) ≤ (y normal + 3/4) / (1/8) := (le_div_iff₀ (by norm_num)).mpr (by linarith)
  have h₂ : (1 : ℝ) ≤ (3 * tb - conformalDepth normal L y) / (tb / 2) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  rw [Real.smoothTransition.one_of_one_le h₁, Real.smoothTransition.one_of_one_le h₂, one_mul]

theorem cylinderCutoff_eq_one_eventually {L tb : ℝ} (htb : 0 < tb) {y : (X dim)}
    (hlo : -(5/8 : ℝ) < y normal) (hhi : conformalDepth normal L y < (5/2) * tb) :
    cylinderCutoff normal L tb =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
  have h₁ := (isOpen_lt continuous_const ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).mem_nhds hlo
  have h₂ := (isOpen_lt ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const).mem_nhds hhi
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  exact (cylinderCutoff_eq_one (normal := normal)) htb hz₁.le hz₂.le

theorem cylinderCutoff_tsupport_subset_interior {L tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) :
    tsupport (cylinderCutoff normal L tb) ⊆ interior (coordinateCylinder normal) := by
  let S : Set (X dim) := {y | -(3/4 : ℝ) ≤ y normal} ∩ {y | conformalDepth normal L y ≤ 3 * tb}
  have hS : IsClosed S := (isClosed_le continuous_const ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).inter
    (isClosed_le ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const)
  have hsub : Function.support (cylinderCutoff normal L tb) ⊆ S := by
    intro y hy
    change cylinderCutoff normal L tb y ≠ 0 at hy
    change -(3/4 : ℝ) ≤ y normal ∧ conformalDepth normal L y ≤ 3 * tb
    refine ⟨le_of_not_gt (fun hlo => ?_), le_of_not_gt (fun hhi => ?_)⟩
    · apply hy
      have hdiv : (y normal + 3/4) / (1/8) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
      rw [cylinderCutoff, Real.smoothTransition.zero_of_nonpos hdiv, zero_mul]
    · apply hy
      simp [cylinderCutoff, Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity) :
          (3 * tb - conformalDepth normal L y) / (tb / 2) ≤ 0)]
  apply (closure_minimal hsub hS).trans
  intro y hy
  have hlo : -(3/4 : ℝ) ≤ y normal := hy.1
  have hp := hm y hy.2
  simp only [parabolicHeight, tubeHeight, zero_add, one_mul] at hp
  exact (mem_coordinateCylinder_interior (normal := normal)) (by linarith) (by linarith)
    (by linarith [transversePair_nonneg normal y])

theorem cylinderCutoff_differential_tsupport {L tb : ℝ} (htb : 0 < tb) :
    tsupport (fderiv ℝ (cylinderCutoff normal L tb)) ⊆
      {y | y normal < -(1/4 : ℝ)} ∪ {y | tb < conformalDepth normal L y} := by
  intro y hy
  by_contra hout
  have hn : ¬ (y normal < -(1/4 : ℝ) ∨ tb < conformalDepth normal L y) := hout
  push Not at hn
  let U : Set (X dim) := {z | -(5/8 : ℝ) < z normal} ∩ {z | conformalDepth normal L z < (5/2) * tb}
  have hU : IsOpen U := (isOpen_lt continuous_const
    ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).inter
    (isOpen_lt ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const)
  have hyU : y ∈ U := by
    change -(5/8 : ℝ) < y normal ∧ conformalDepth normal L y < (5/2) * tb
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
  have hzero : ∀ z ∈ U, fderiv ℝ (cylinderCutoff normal L tb) z = 0 := by
    intro z hz
    rw [((cylinderCutoff_eq_one_eventually (normal := normal)) htb hz.1 hz.2).fderiv_eq]
    simp
  obtain ⟨z, hz, hzU⟩ := ((mem_closure_iff_frequently.mp hy).and_eventually (hU.mem_nhds hyU)).exists
  exact hz (hzero z hzU)

theorem hasCompactSupport_cylinderCutoff {L tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) :
    HasCompactSupport (cylinderCutoff normal L tb) :=
  (isCompact_coordinateCylinder (normal := normal)).of_isClosed_subset (isClosed_tsupport _)
    (((cylinderCutoff_tsupport_subset_interior (normal := normal)) htb hm).trans interior_subset)

theorem cylinderCore_subset_interior {L tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) :
    cylinderCore normal L tb ⊆ interior (coordinateCylinder normal) := by
  intro y hy
  have hlo : -(1/2 : ℝ) ≤ y normal := hy.2.1
  have hdep : conformalDepth normal L y ≤ 2 * tb := hy.2.2
  have hp := hm y (by linarith)
  simp only [parabolicHeight, tubeHeight, zero_add, one_mul] at hp
  exact (mem_coordinateCylinder_interior (normal := normal)) (by linarith) (by linarith)
    (by linarith [transversePair_nonneg normal y])

theorem origin_mem_interior_cylinderCore {L tb : ℝ} (hL : 0 < L) (htb : 0 < tb) :
    (0 : (X dim)) ∈ interior (cylinderCore normal L tb) := by
  have hn₁ : (coordinateCylinder normal) ∈ 𝓝 (0 : (X dim)) :=
    mem_interior_iff_mem_nhds.mp ((mem_coordinateCylinder_interior (normal := normal)) (by simp [transversePair]) (by simp) (by simp))
  have hn₂ : {y : (X dim) | -(1/2 : ℝ) < y normal} ∈ 𝓝 (0 : (X dim)) :=
    (isOpen_lt continuous_const ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).mem_nhds (by simp)
  have hn₃ : {y : (X dim) | conformalDepth normal L y < 2 * tb} ∈ 𝓝 (0 : (X dim)) :=
    (isOpen_lt ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const).mem_nhds
      (show conformalDepth normal L 0 < 2 * tb from ((conformalDepth_at_origin_neg (normal := normal)) hL).trans (by positivity))
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (inter_mem hn₁ (inter_mem hn₂ hn₃)) ?_
  intro y hy
  exact ⟨hy.1, (show -(1/2 : ℝ) < y normal from hy.2.1).le,
    (show conformalDepth normal L y < 2 * tb from hy.2.2).le⟩

theorem exists_cylinderCore_cutoff_buffer {L tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) :
    ∃ a > 0, ∀ y ∈ cylinderCore normal L tb, closedBall y a ⊆ (coordinateCylinder normal) ∧
      ball y a ⊆ interior (coordinateCylinder normal) ∧ EqOn (cylinderCutoff normal L tb) 1 (ball y a) := by
  let U : Set (X dim) := interior (coordinateCylinder normal) ∩
    ({y | -(5/8 : ℝ) < y normal} ∩ {y | conformalDepth normal L y < (5/2) * tb})
  have hU : IsOpen U := isOpen_interior.inter ((isOpen_lt continuous_const
    ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous)).inter
    (isOpen_lt ((contDiff_conformalDepth (normal := normal)) L).continuous continuous_const))
  have hK : cylinderCore normal L tb ⊆ U := by
    intro y hy
    have hlo : -(1/2 : ℝ) ≤ y normal := hy.2.1
    have hdep : conformalDepth normal L y ≤ 2 * tb := hy.2.2
    change y ∈ interior (coordinateCylinder normal) ∧ -(5/8 : ℝ) < y normal ∧ conformalDepth normal L y < (5/2) * tb
    exact ⟨(cylinderCore_subset_interior (normal := normal)) htb hm hy, by linarith, by linarith⟩
  obtain ⟨a, ha, hball⟩ := ((isCompact_cylinderCore (normal := normal)) L tb).exists_thickening_subset_open hU hK
  refine ⟨a / 2, by positivity, fun y hy => ?_⟩
  have hclosed : closedBall y (a / 2) ⊆ U := by
    intro z hz
    apply hball
    exact mem_thickening_iff.mpr ⟨y, hy, (mem_closedBall.mp hz).trans_lt (by linarith)⟩
  refine ⟨fun z hz => interior_subset (hclosed hz).1, fun z hz => (hclosed (ball_subset_closedBall hz)).1, ?_⟩
  intro z hz
  have hzU := hclosed (ball_subset_closedBall hz)
  exact (cylinderCutoff_eq_one (normal := normal)) htb (show -(5/8 : ℝ) < z normal from hzU.2.1).le
    (show conformalDepth normal L z < (5/2) * tb from hzU.2.2).le

end CalderonN
