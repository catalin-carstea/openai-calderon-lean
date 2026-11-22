module

public import Proof.CalderonN.CylinderSeed
public import Proof.CalderonN.ShrinkingRadiusParameter

import Proof.CalderonN.CompactBounds
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim]
variable {normal : I dim}

open FixedTube

set_option maxHeartbeats 450000 in
/-- A fixed positive normal radius separates the top and the high
boundary from the shrinking front. The larger upper parameter leaves
the starting level inside an open collar. -/
theorem exists_cylinder_radius_seed_with_high
    {R ρ tb : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (htb : 0 < tb) (p : ℕ)
    (hm : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hcap : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
      shrinkingRadius R p (conformalDepth normal 4) a y ≤ ρ/2) :
    ∃ upper r₀ : ℝ, 1 < upper ∧ 0 < r₀ ∧
      (∀ a ∈ Ioo (0 : ℝ) upper, ∀ y ∈ coordinateCylinder normal,
        shrinkingRadius R p (conformalDepth normal 4) a y < ρ) ∧
      (∀ a ∈ Ioo (1 : ℝ) upper, ∀ y ∈ coordinateCylinder normal,
        r₀ < shrinkingRadius R p (conformalDepth normal 4) a y) ∧
      (∀ a > 0, ∀ y ∈ coordinateCylinder normal \ interior (coordinateCylinder normal),
        -(1/4 : ℝ) ≤ y normal → r₀ < shrinkingRadius R p (conformalDepth normal 4) a y) ∧
      (∀ a > 0, ∀ y : (X dim), tb ≤ conformalDepth normal 4 y →
        r₀ < shrinkingRadius R p (conformalDepth normal 4) a y) := by
  let r := shrinkingRadius R p (conformalDepth normal 4)
  have hr : ContDiffOn ℝ ∞ (fun z : ℝ × (X dim) => r z.1 z.2) (Ioi 0 ×ˢ (univ : Set (X dim))) :=
    contDiffOn_shrinkingRadius_parameter (contDiff_conformalDepth (normal := normal) 4).contDiffOn R p
  have hPos (a : ℝ) (ha : 0 < a) (y : (X dim)) : 0 < r a y :=
    mul_pos hR (pow_pos (softplus_pos ha _) _)
  have hAt (y : (X dim)) : ContinuousAt (fun z : ℝ × (X dim) => r z.1 z.2) (1,y) :=
    (hr.contDiffAt (((isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).prod isOpen_univ).mem_nhds
      ⟨zero_lt_one,mem_univ _⟩)).continuousAt
  have htop : ∀ᶠ a in 𝓝 (1 : ℝ), ∀ y ∈ coordinateCylinder normal, r a y < ρ := by
    apply (isCompact_coordinateCylinder (normal := normal)).eventually_forall_of_forall_eventually
    intro y hy
    have hh := (hcap 1 ⟨zero_lt_one,le_rfl⟩ y hy).trans_lt (half_lt_self hρ)
    exact (hAt y).eventually (Iio_mem_nhds hh)
  obtain ⟨a,ha,haTop⟩ := Metric.eventually_nhds_iff.mp htop
  let upper := 1+a/2
  have hUpper : 1 < upper := by dsimp [upper]; linarith
  have hCont : Continuous (r 1) := continuousOn_univ.mp
    (hr.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨zero_lt_one,mem_univ _⟩))
  obtain ⟨d,hd,hmin⟩ := Carleman.exists_pos_lower_of_compact (isCompact_coordinateCylinder (normal := normal))
    hCont.continuousOn (fun y _ => hPos 1 zero_lt_one y)
  let r₀ := min (d/2) (R*tb^p/2)
  have hr₀ : 0 < r₀ := lt_min (half_pos hd) (by positivity)
  have hHigh (b : ℝ) (hb : 0 < b) (y : (X dim)) (hy : tb ≤ conformalDepth normal 4 y) : r₀ < r b y := by
    have hRad := shrinkingRadius_ge_of_cylinderDepth htb hR.le hb p hy
    exact ((min_le_right _ _).trans_lt (half_lt_self (by positivity : 0 < R*tb^p))).trans_le hRad
  refine ⟨upper,r₀,hUpper,hr₀,?_,?_,?_,hHigh⟩
  · intro b hb y hy
    by_cases h : b ≤ 1
    · exact (hcap b ⟨hb.1,h⟩ y hy).trans_lt (half_lt_self hρ)
    · apply haTop _ y hy
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr (lt_of_not_ge h))]
      have hh := hb.2
      dsimp [upper] at hh
      linarith
  · intro b hb y hy
    have hmono : r 1 y ≤ r b y := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (softplus_pos zero_lt_one _).le
        ((strictMonoOn_softplus_scale (conformalDepth normal 4 y)).monotoneOn zero_lt_one
          (zero_lt_one.trans hb.1) hb.1.le) _) hR.le
    exact ((min_le_left _ _).trans_lt (half_lt_self hd)).trans_le ((hmin y hy).trans hmono)
  · intro b hb y hy hY
    have hdepth : tb ≤ conformalDepth normal 4 y := by
      by_contra! h
      have hpar := hm y (by linarith)
      have hy1 := hy.1
      change parabolicHeight normal y < 1/4 at hpar
      have hside : transversePair normal y y < 1 := by
        simp only [parabolicHeight, tubeHeight, zero_add, one_mul] at hpar
        linarith
      have hhi : y normal < 1 := by
        simp only [parabolicHeight, tubeHeight, zero_add, one_mul] at hpar
        nlinarith [transversePair_nonneg normal y]
      exact hy.2 (mem_coordinateCylinder_interior (normal := normal) hside (by linarith) hhi)
    exact hHigh b hb y hdepth

/-- A fixed positive normal radius separates the top and the high
boundary from the shrinking front. The larger upper parameter leaves
the starting level inside an open collar. -/
theorem exists_cylinder_radius_seed
    {R ρ tb : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (htb : 0 < tb) (p : ℕ)
    (hm : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hcap : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
      shrinkingRadius R p (conformalDepth normal 4) a y ≤ ρ/2) :
    ∃ upper r₀ : ℝ, 1 < upper ∧ 0 < r₀ ∧
      (∀ a ∈ Ioo (0 : ℝ) upper, ∀ y ∈ coordinateCylinder normal,
        shrinkingRadius R p (conformalDepth normal 4) a y < ρ) ∧
      (∀ a ∈ Ioo (1 : ℝ) upper, ∀ y ∈ coordinateCylinder normal,
        r₀ < shrinkingRadius R p (conformalDepth normal 4) a y) ∧
      (∀ a > 0, ∀ y ∈ coordinateCylinder normal \ interior (coordinateCylinder normal),
        -(1/4 : ℝ) ≤ y normal → r₀ < shrinkingRadius R p (conformalDepth normal 4) a y) := by
  obtain ⟨u,r,hu,hr,hCap,hTop,hSide,_⟩ := exists_cylinder_radius_seed_with_high hR hρ htb p hm hcap
  exact ⟨u,r,hu,hr,hCap,hTop,hSide⟩

end CalderonN.MovingSphere
