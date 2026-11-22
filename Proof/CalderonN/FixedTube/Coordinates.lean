module

public import Proof.CalderonN.SphereCoordinates
public import Proof.CalderonN.FixedTube.JetContinuity
public import Proof.CalderonN.FixedTube.CompactSweep
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

abbrev TubeBase (dim : ℕ) := (X dim) × sphere (0 : (X dim)) 1

/-- Polar coordinates on the positive-height region off the diagonal.
The vertical coordinate is the tube level rather than the Euclidean radius. -/
def tubeCoordinates (normal : I dim) (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    OpenPartialHomeomorph ((X dim) × (X dim)) ((TubeBase dim) × ℝ) where
  toFun p := ((p.2,sphereDirection (p.1-p.2)),‖p.1-p.2‖ / tubeHeight normal M e0 p.2 ^ (1+σ))
  invFun q := (q.1.1 + tubeRadius normal M e0 q.2 σ q.1.1 • (q.1.2 : (X dim)), q.1.1)
  source := {p | 0 < tubeHeight normal M e0 p.2 ∧ p.1 ≠ p.2}
  target := {q | 0 < tubeHeight normal M e0 q.1.1 ∧ 0 < q.2}
  map_source' := by
    intro p hp
    exact ⟨hp.1, div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp.2)) (Real.rpow_pos_of_pos hp.1 _)⟩
  map_target' := by
    intro q hq
    have hr : 0 < tubeRadius normal M e0 q.2 σ q.1.1 :=
      mul_pos hq.2 (Real.rpow_pos_of_pos hq.1 _)
    have hu := mem_sphere_zero_iff_norm.mp q.1.2.property
    refine ⟨hq.1, fun h => ?_⟩
    have hs := add_left_cancel (h.trans (add_zero _).symm)
    have hn : ‖(q.1.2 : (X dim))‖ ≠ 0 := by rw [hu]; exact one_ne_zero
    exact (smul_ne_zero hr.ne' (norm_ne_zero_iff.mp hn)) hs
  left_inv' := by
    intro p hp
    have hs := sub_ne_zero.mpr hp.2
    have hn := norm_ne_zero_iff.mpr hs
    have ht := Real.rpow_pos_of_pos hp.1 (1+σ)
    apply Prod.ext
    · change p.2 + tubeRadius normal M e0 (‖p.1-p.2‖ / tubeHeight normal M e0 p.2 ^ (1+σ)) σ p.2 •
        (sphereDirection (p.1-p.2) : (X dim)) = p.1
      rw [tubeRadius, div_mul_cancel₀ _ ht.ne', sphereDirection_val hs, smul_smul,
        mul_inv_cancel₀ hn, one_smul]
      abel
    · rfl
  right_inv' := by
    intro q hq
    let r := tubeRadius normal M e0 q.2 σ q.1.1
    have ht := Real.rpow_pos_of_pos hq.1 (1+σ)
    have hr : 0 < r := mul_pos hq.2 ht
    have hu := mem_sphere_zero_iff_norm.mp q.1.2.property
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (sphereDirection (q.1.1 + r • (q.1.2 : (X dim)) - q.1.1) : (X dim)) = (q.1.2 : (X dim))
        rw [add_sub_cancel_left, sphereDirection_pos_smul hu hr]
    · change ‖q.1.1 + r • (q.1.2 : (X dim)) - q.1.1‖ / tubeHeight normal M e0 q.1.1 ^ (1+σ) = q.2
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one,
        show r = q.2 * tubeHeight normal M e0 q.1.1 ^ (1+σ) from rfl, mul_div_cancel_right₀ _ ht.ne']
  open_source := (isOpen_lt continuous_const
    ((contDiff_tubeHeight (normal := normal) M e0).continuous.comp continuous_snd)).inter
    (isOpen_ne_fun continuous_fst continuous_snd)
  open_target := (isOpen_lt continuous_const
    ((contDiff_tubeHeight (normal := normal) M e0).continuous.comp continuous_fst.fst)).inter
    (isOpen_lt continuous_const continuous_snd)
  continuousOn_toFun := by
    let S : Set ((X dim) × (X dim)) := {p | 0 < tubeHeight normal M e0 p.2 ∧ p.1 ≠ p.2}
    rw [continuousOn_iff_continuous_domRestrict]
    have cp : Continuous (fun p : S => (p : (X dim) × (X dim))) := continuous_subtype_val
    have cD : Continuous (fun p : S => sphereDirection ((p : (X dim) × (X dim)).1 - (p : (X dim) × (X dim)).2)) := by
      apply continuousOn_sphereDirection.comp_continuous (cp.fst.sub cp.snd)
      intro p
      simpa using sub_ne_zero.mpr p.property.2
    have cr : Continuous (fun p : S => tubeHeight normal M e0 (p : (X dim) × (X dim)).2 ^ (1+σ)) :=
      ((contDiff_tubeHeight (normal := normal) M e0).continuous.comp cp.snd).rpow_const
        (fun p => Or.inl p.property.1.ne')
    exact (cp.snd.prodMk cD).prodMk ((cp.fst.sub cp.snd).norm.div cr fun p =>
      (Real.rpow_pos_of_pos p.property.1 _).ne')
  continuousOn_invFun :=
    ((continuous_fst.fst.add
      (((tubeRadius_continuous (normal := normal) M e0 σ hσ).comp (continuous_snd.prodMk continuous_fst.fst)).smul
        (continuous_subtype_val.comp continuous_fst.snd))).prodMk continuous_fst.fst).continuousOn

theorem tubeCoordinates_source (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    (tubeCoordinates normal M e0 σ hσ).source = {p : (X dim) × (X dim) | 0 < tubeHeight normal M e0 p.2 ∧ p.1 ≠ p.2} := by
  unfold tubeCoordinates
  rfl

theorem tubeCoordinates_center (M e0 σ : ℝ) (hσ : 0 ≤ σ) (p : (X dim) × (X dim)) :
    (tubeCoordinates normal M e0 σ hσ p).1.1 = p.2 := by
  unfold tubeCoordinates
  rfl

theorem tubeCoordinates_level (M e0 σ : ℝ) (hσ : 0 ≤ σ) (p : (X dim) × (X dim)) :
    (tubeCoordinates normal M e0 σ hσ p).2 = ‖p.1-p.2‖ / tubeHeight normal M e0 p.2 ^ (1+σ) := by
  unfold tubeCoordinates
  rfl

theorem tubeCoordinates_target (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    (tubeCoordinates normal M e0 σ hσ).target = {q : (TubeBase dim) × ℝ | 0 < tubeHeight normal M e0 q.1.1 ∧ 0 < q.2} := by
  unfold tubeCoordinates
  rfl

theorem tubeCoordinates_symm_apply (M e0 σ : ℝ) (hσ : 0 ≤ σ) (q : (TubeBase dim) × ℝ) :
    (tubeCoordinates normal M e0 σ hσ).symm q =
      (q.1.1 + tubeRadius normal M e0 q.2 σ q.1.1 • (q.1.2 : (X dim)), q.1.1) := by
  unfold tubeCoordinates
  rfl

theorem tubePhase_along_vertical {M e0 σ a b : ℝ} (hσ : 0 ≤ σ) (z : (TubeBase dim)) (ht : 0 < tubeHeight normal M e0 z.1) (hb : 0 ≤ b) :
    tubePhase normal M e0 a σ ((tubeCoordinates normal M e0 σ hσ).symm (z,b)) =
      (b ^ 2 - a ^ 2) * (tubeHeight normal M e0 z.1 ^ (1 + σ)) ^ 2 / 2 := by
  have hr : 0 ≤ tubeRadius normal M e0 b σ z.1 := mul_nonneg hb (Real.rpow_nonneg ht.le _)
  rw [tubeCoordinates_symm_apply, tubePhase, add_sub_cancel_left, norm_smul,
    mem_sphere_zero_iff_norm.mp z.2.property, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  simp only [tubeRadius]
  ring

end CalderonN.FixedTube
