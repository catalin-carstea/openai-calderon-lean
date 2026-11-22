module

public import Proof.CalderonN.FixedTube.Coordinates
public import Proof.CalderonN.FixedTube.DilatedStrict
public import Proof.CalderonN.ProductPhaseSweep

import Proof.CalderonN.FixedTube.JetContinuity
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

@[expose] def tubeBaseSet (normal : I dim) (M e0 B T0 : ℝ) : Set (TubeBase dim) :=
  {z | -B - 1 ≤ z.1 normal ∧ tubeHeight normal M e0 z.1 ≤ T0}

private theorem isCompact_tubeCenters {M e0 B T0 : ℝ} (he0 : 0 < e0) (hB : 0 ≤ B) :
    IsCompact {y : (X dim) | -B - 1 ≤ y normal ∧ tubeHeight normal M e0 y ≤ T0} := by
  let D := |M| + |T0| + B + 1
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hc₂ := (EuclideanSpace.proj (𝕜 := ℝ) normal : (X dim) →L[ℝ] ℝ).continuous
  have hc := (contDiff_tubeHeight (normal := normal) M e0).continuous
  apply isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const hc₂).inter (isClosed_le hc continuous_const)
  · apply Metric.isBounded_closedBall (x := (0 : (X dim))) (r := Real.sqrt (D/e0 + D^2)) |>.subset
    intro y hy
    have h0 := mul_nonneg he0.le (transversePair_nonneg normal y)
    obtain ⟨hy₂,hyh⟩ := hy
    simp only [tubeHeight] at hyh
    have hyh' : transversePair normal y y ≤ D/e0 := by
      rw [le_div_iff₀ he0]
      dsimp only [D]
      linarith [neg_abs_le M,le_abs_self T0]
    have hv : y normal ^ 2 ≤ D^2 := by
      apply sq_le_sq'
      · dsimp only [D]
        linarith [abs_nonneg M,abs_nonneg T0]
      · dsimp only [D]
        linarith [neg_abs_le M,le_abs_self T0]
    rw [mem_closedBall,dist_zero_right,norm_eq_transversePair normal y]
    exact Real.sqrt_le_sqrt (add_le_add hyh' hv)

theorem isCompact_tubeBaseSet {M e0 B T0 : ℝ} (he0 : 0 < e0) (hB : 0 ≤ B) :
    IsCompact (tubeBaseSet normal M e0 B T0) := by
  let : CompactSpace ↥(sphere (0 : (X dim)) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have h := (isCompact_tubeCenters (normal := normal) (M := M) (T0 := T0) he0 hB).prod
    (isCompact_univ : IsCompact (univ : Set ↥(sphere (0 : (X dim)) 1)))
  convert h using 1
  ext z
  simp [tubeBaseSet]

theorem mem_interior_tubeBaseSet {M e0 B T0 : ℝ} {z : (TubeBase dim)}
    (hy : -B - 1 < z.1 normal) (ht : tubeHeight normal M e0 z.1 < T0) :
    z ∈ interior (tubeBaseSet normal M e0 B T0) := by
  have hyc := (EuclideanSpace.proj (𝕜 := ℝ) normal : (X dim) →L[ℝ] ℝ).continuous.comp
    (continuous_fst : Continuous (Prod.fst : (TubeBase dim) → (X dim)))
  have htc := (contDiff_tubeHeight (normal := normal) M e0).continuous.comp (continuous_fst :
    Continuous (Prod.fst : (TubeBase dim) → (X dim)))
  let V : Set (TubeBase dim) := {z | -B - 1 < z.1 normal ∧ tubeHeight normal M e0 z.1 < T0}
  have hV : IsOpen V := (isOpen_lt (f := fun _ : (TubeBase dim) => -B - 1) continuous_const hyc).inter
    (isOpen_lt htc (g := fun _ : (TubeBase dim) => T0) continuous_const)
  have hsub : V ⊆ tubeBaseSet normal M e0 B T0 := fun _ h => ⟨h.1.le,h.2.le⟩
  exact interior_maximal hsub hV (show z ∈ V from ⟨hy,ht⟩)

/-- The literal fixed-separation tube is covered by qualitative
continuation from the coarse seed with the displayed height bound. -/
theorem exists_productSolution_fixedTube
    {M e0 B T0 σ c0 lo amin amax upper : ℝ}
    (he0 : 0 < e0) (hB : 0 ≤ B) (hM : B + 3 < M) (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hlo₀ : 0 ≤ lo) (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < upper)
    (hamax : 2/c0+1 ≤ amax) (htop : 1 < c0 * amin * T0 ^ σ)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {S : Set ((X dim) × (X dim))} (hS : IsOpen S) (Fseed : (X dim) × (X dim) → ℝ)
    (hFseed : ProductSolutionOn g₁ g₂ S Fseed)
    (hcoarse : ∀ a ∈ Ioo lo upper, ∀ z ∈ tubeBaseSet normal M e0 B T0,
      let p := tubePoint normal M e0 σ (a,z.1,(z.2 : (X dim)))
      p ∈ S ↔ min (p.1 normal) (p.2 normal) < c0 * ‖p.1-p.2‖)
    (hstrict : ∀ a ∈ Icc amin amax, ∀ z ∈ tubeBaseSet normal M e0 B T0,
      let p := tubePoint normal M e0 σ (a,z.1,(z.2 : (X dim)))
      c0 * ‖p.1-p.2‖ ≤ min (p.1 normal) (p.2 normal) →
        ProductStrictHessianAt g₁ g₂ (tubePhase normal M e0 a σ) p) :
    ∃ O : Set ((X dim) × (X dim)), IsOpen O ∧
      S ∪ (tubeCoordinates normal M e0 σ hσ).symm '' (tubeBaseSet normal M e0 B T0 ×ˢ Icc amin amax) ⊆ O ∧
      ∃ G, ProductSolutionOn g₁ g₂ O G ∧ EqOn G Fseed S := by
  let e := tubeCoordinates normal M e0 σ hσ
  let K := tubeBaseSet normal M e0 B T0
  have hK : IsCompact K := isCompact_tubeBaseSet he0 hB
  have hlevel (a : ℝ) (ha : a ∈ Icc amin amax) : a ∈ Ioo lo upper :=
    ⟨hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
  have hheight {z : (TubeBase dim)} (hz : z ∈ K) : 1 ≤ tubeHeight normal M e0 z.1 :=
    (tube_base_height he0.le hM hz.1 hz.2).1
  have hpos {z : (TubeBase dim)} (hz : z ∈ K) : 0 < tubeHeight normal M e0 z.1 :=
    zero_lt_one.trans_le (hheight hz)
  have hA {a : ℝ} (ha : a ∈ Ioo lo upper) : 0 < a := hlo₀.trans_lt ha.1
  have hM₀ : 0 ≤ M := by linarith
  have hpoint (z : (TubeBase dim)) (a : ℝ) : e.symm (z,a) = tubePoint normal M e0 σ (a,z.1,(z.2 : (X dim))) :=
    tubeCoordinates_symm_apply (normal := normal) M e0 σ hσ (z,a)
  have htarget : K ×ˢ Ioo lo upper ⊆ e.target := by
    intro q hq
    rw [show e.target = _ from tubeCoordinates_target (normal := normal) M e0 σ hσ]
    exact ⟨hpos hq.1,hA hq.2⟩
  have habove : e.symm '' (K ×ˢ Ioo amax upper) ⊆ S := by
    rintro _ ⟨⟨z,a⟩,⟨hz,ha⟩,rfl⟩
    rw [hpoint]
    exact (hcoarse a ⟨(hlo.trans_le hab).trans ha.1,ha.2⟩ z hz).mpr
      (tube_amax_level_in_seed hc0 hM₀ he0.le (hheight hz) hσ (hamax.trans ha.1.le)
        (mem_sphere_zero_iff_norm.mp z.2.property))
  have hside : e.symm '' ((K \ interior K) ×ˢ Icc amin amax) ⊆ S := by
    rintro _ ⟨⟨z,a⟩,⟨⟨hz,hzi⟩,ha⟩,rfl⟩
    have hn := mem_sphere_zero_iff_norm.mp z.2.property
    have hza := hlevel a ha
    rw [hpoint]
    apply (hcoarse a hza z hz).mpr
    by_cases hbottom : -B - 1 < z.1 normal
    · have heq : tubeHeight normal M e0 z.1 = T0 := le_antisymm hz.2
        (not_lt.mp fun ht => hzi (mem_interior_tubeBaseSet hbottom ht))
      exact tube_top_face_in_seed hc0 hM₀ he0.le (hpos hz) (hA ⟨hlo,hab.trans_lt hhi⟩).le
        ha.1 (by rwa [heq]) hn
    · have hy : z.1 normal < 0 := by linarith [not_lt.mp hbottom]
      exact tube_bottom_face_in_seed hc0 (mul_pos (hA hza) (Real.rpow_pos_of_pos (hpos hz) _)) hy hn
  have hup (z : (TubeBase dim)) (hz : z ∈ K) (s t : ℝ) (hs : s ∈ Ioo lo upper) (ht : t ∈ Ioo lo upper)
      (hst : s ≤ t) (hseed : e.symm (z,s) ∈ S) : e.symm (z,t) ∈ S := by
    rw [hpoint] at hseed ⊢
    have htpos := Real.rpow_pos_of_pos (hpos hz) (1+σ)
    exact (hcoarse t ht z hz).mpr (tube_seed_upward
      (mem_sphere_zero_iff_norm.mp z.2.property) hc0 (mul_pos (hA hs) htpos).le
      (mul_le_mul_of_nonneg_right hst htpos.le) ((hcoarse s hs z hz).mp hseed))
  apply exists_productSolution_across_compact_phase_cylinder e hK hS hlo hab hhi htarget
    habove hside hup hg₁ hg₂ Fseed hFseed (fun a => tubePhase normal M e0 a σ)
  · intro a _
    rintro _ ⟨q,hq,rfl⟩
    exact (contDiffAt_tubePhase (normal := normal) (a := a) (σ := σ)
      (z := e.symm q) (by rw [hpoint]; exact hpos (interior_subset hq.1))).contDiffWithinAt
  · intro a ha z hz
    rw [show e = tubeCoordinates normal M e0 σ hσ from rfl,
      tubePhase_along_vertical (normal := normal) hσ z (hpos (interior_subset hz)) (hA (hlevel a ha)).le]
    ring
  · intro a ha z hz t ht
    rw [show e = tubeCoordinates normal M e0 σ hσ from rfl,
      tubePhase_along_vertical (normal := normal) hσ z (hpos (interior_subset hz)) (hA ht).le]
    have hp : 0 < (tubeHeight normal M e0 z.1 ^ (1 + σ)) ^ 2 :=
      pow_pos (Real.rpow_pos_of_pos (hpos (interior_subset hz)) _) 2
    rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right hp,sub_pos,
      pow_lt_pow_iff_left₀ (hA (hlevel a ha)).le (hA ht).le two_ne_zero]
  · intro a ha z hz hns
    rw [hpoint] at hns ⊢
    exact hstrict a ha z (interior_subset hz) (le_of_not_gt fun h =>
      hns ((hcoarse a (hlevel a ha) z (interior_subset hz)).mpr h))

end CalderonN.FixedTube
