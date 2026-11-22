module

public import Proof.CalderonN.HarmonicInterpolationChain

import Proof.CalderonN.FixedTube.RadialCarleman
import Proof.CalderonN.FixedTube.RadialCollars
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 450000 in
/-- Uniform three-ball interpolation on a thin collar for a smooth
family near the Euclidean chart metric. The exponent increases to one as the inner and
target weight levels approach each other. -/
theorem exists_parameter_radial_interpolation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (g : P → (MetricField dim)) (p₀ : P) (hg : ∀ p, SmoothMetric univ (g p))
    (hbg : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g z.1) z.2 i j))
    (hg₀ : g p₀ = fun _ => (1 : (Mat dim))) (c : (X dim))
    {a b s t u v d : ℝ}
    (ha : 0 < a) (hab : a < b) (hbs : b < s) (hst : s ≤ t)
    (htu : t < u) (huv : u < v) (hvd : v < d) (hthin : v^3 < 2*a^3) :
    ∃ R A : ℝ, 0 < R ∧ 0 < A ∧
      ∀ p ∈ closedBall p₀ R,
      let hD : IsOpen (ball c d) := isOpen_ball
      let hgD : SmoothMetric (ball c d) (g p) :=
        ⟨fun i j => ((hg p).1 i j).mono (subset_univ _),
          fun x _ => (hg p).2 x (mem_univ x)⟩
      HarmonicInterpolation hD hgD (ball_subset_ball (hst.trans (htu.trans (huv.trans hvd)).le))
        (ball_subset_ball ((htu.trans (huv.trans hvd)).le)) A
        ((t⁻¹-u⁻¹)/(a⁻¹-u⁻¹)) := by
  let D := ball c d
  let S := ball c s
  let O := ball c t \ ball c b
  let B := closedAnnulus c u v
  let H := closedAnnulus c a b
  let K := closedAnnulus c a v
  have hK : IsCompact K := isCompact_closedAnnulus c a v
  have hB : IsCompact B := isCompact_closedAnnulus c u v
  have hH : IsCompact H := isCompact_closedAnnulus c a b
  have hbt : b < t := hbs.trans_le hst
  have hav : a < v := hab.trans (hbt.trans (htu.trans huv))
  have htd : t < d := htu.trans (huv.trans hvd)
  have hSD : S ⊆ D := ball_subset_ball (hst.trans htd.le)
  have hTD : ball c t ⊆ D := ball_subset_ball htd.le
  have hOD : O ⊆ D := sdiff_subset.trans hTD
  have hBD : B ⊆ D := sdiff_subset.trans (closedBall_subset_ball hvd)
  have hHS : H ⊆ S := sdiff_subset.trans (closedBall_subset_ball hbs)
  have hKD : K ⊆ D := sdiff_subset.trans (closedBall_subset_ball hvd)
  have hBK : B ⊆ K := fun x hx => mem_closedAnnulus.mpr
    ⟨(hab.trans (hbt.trans htu)).le.trans (mem_closedAnnulus.mp hx).1,(mem_closedAnnulus.mp hx).2⟩
  have hHK : H ⊆ K := fun x hx => mem_closedAnnulus.mpr
    ⟨(mem_closedAnnulus.mp hx).1,(mem_closedAnnulus.mp hx).2.trans (hbt.trans (htu.trans huv)).le⟩
  have hOK : O ⊆ K := fun x hx => mem_closedAnnulus.mpr
    ⟨hab.le.trans (not_lt.mp (by simpa [mem_ball,dist_eq_norm] using hx.2)),
      (by simpa [mem_ball,dist_eq_norm] using hx.1 : ‖x-c‖ < t).le.trans (htu.trans huv).le⟩
  obtain ⟨R,C,τ₀,hR,hC,hτ,φ,hφ,hφrad,hEst⟩ := exists_compact_radialCarleman g p₀ hg hbg hg₀ c
    ha hav.le hthin hK (fun x hx => (mem_closedAnnulus.mp hx).1)
    (fun x hx => (mem_closedAnnulus.mp hx).2)
  obtain ⟨χ,hχ,hχc,hχK,hχ1,hχtrans⟩ := exists_radialCollarCutoff c hab huv
  have hχO (x : (X dim)) (hx : x ∈ O) : χ x = 1 :=
    hχ1 x ⟨ball_subset_closedBall (ball_subset_ball htu.le hx.1),hx.2⟩
  have hφB (x : (X dim)) (hx : x ∈ B) : φ x ≤ u⁻¹ := by
    rw [(hφrad x (hBK hx)).eq_of_nhds,radialWeight_eq_inv_norm]
    exact inv_anti₀ (ha.trans (hab.trans (hbt.trans htu))) (mem_closedAnnulus.mp hx).1
  have hφH (x : (X dim)) (hx : x ∈ H) : φ x ≤ a⁻¹ := by
    rw [(hφrad x (hHK hx)).eq_of_nhds,radialWeight_eq_inv_norm]
    exact inv_anti₀ ha (mem_closedAnnulus.mp hx).1
  have hφO (x : (X dim)) (hx : x ∈ O) : t⁻¹ ≤ φ x := by
    rw [(hφrad x (hOK hx)).eq_of_nhds,radialWeight_eq_inv_norm]
    exact inv_anti₀ (ha.trans_le (mem_closedAnnulus.mp (hOK hx)).1)
      (by simpa [mem_ball,dist_eq_norm] using (mem_ball.mp hx.1).le)
  have hBO : u⁻¹ < t⁻¹ := inv_strictAnti₀ (ha.trans (hab.trans hbt)) htu
  have hOH : t⁻¹ < a⁻¹ := inv_strictAnti₀ ha (hab.trans hbt)
  let γ := (t⁻¹-u⁻¹)/(a⁻¹-u⁻¹)
  have hγ : γ < 1 := (div_lt_one (sub_pos.mpr (hBO.trans hOH))).mpr
    (sub_lt_sub_right hOH _)
  have hO : MeasurableSet O := isOpen_ball.measurableSet.diff isOpen_ball.measurableSet
  have hD : IsOpen D := isOpen_ball
  let hgD (p : P) : SmoothMetric D (g p) :=
    ⟨fun i j => ((hg p).1 i j).mono (subset_univ _),
      fun x _ => (hg p).2 x (mem_univ x)⟩
  obtain ⟨A,hA,hinterp⟩ := exists_family_harmonicInterpolation_of_collarCutoff
    (isCompact_closedBall p₀ R) g hg hbg hD (isOpen_ball : IsOpen S) hO hSD hOD hB hH hBD hHS hgD
    hχ hχc (hχK.trans hKD) hχK hχO hχtrans hφ.continuous hBO hOH hC.le hτ hφB hφH hφO hEst
  have hCover : ball c t ⊆ S ∪ O := fun x hx => by
    by_cases hb : x ∈ ball c b
    · exact Or.inl (ball_subset_ball hbs.le hb)
    · exact Or.inr ⟨hx,hb⟩
  refine ⟨R,1+A,hR,by positivity,fun p hp q => ?_⟩
  have hnorm := harmonicRestrict_norm_le_of_subset_union hD (hgD p) hSD hOD hTD hO hCover q
  have hobs := observed_norm_le_interpolation (γ := γ)
    (norm_nonneg (harmonicRestrict hD (hgD p) hSD q))
    (harmonicRestrict_norm_le hD (hgD p) hSD q) hγ
  exact hnorm.trans ((add_le_add hobs (hinterp p hp q)).trans_eq (by ring))

set_option maxHeartbeats 500000 in
/-- On the near-plane ball the exponent can exceed any prescribed
number below one. The output extends a positive distance past the
sphere through the limiting plane. -/
theorem exists_nearOne_parameter_radial_interpolation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (g : P → (MetricField dim)) (p₀ : P) (hg : ∀ p, SmoothMetric univ (g p))
    (hbg : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g z.1) z.2 i j))
    (hg₀ : g p₀ = fun _ => (1 : (Mat dim))) (c : (X dim))
    {l γ₀ : ℝ} (hl : 0 < l) (hγ₀ : γ₀ < 1) :
    ∃ δ C γ : ℝ, 0 < δ ∧ δ ≤ l/100 ∧ 0 < C ∧ γ₀ < γ ∧ γ < 1 ∧
      ∀ᶠ p in 𝓝 p₀,
        ∃ (hS : ball c (l-δ) ⊆ ball c (3*l)) (hO : ball c (l+δ) ⊆ ball c (3*l)),
          HarmonicInterpolation isOpen_ball (smoothMetric_restrict (hg p) (subset_univ _)) hS hO C γ := by
  let u := (11/10)*l
  have hlu : l < u := by dsimp [u]; linarith
  let θ (e : ℝ) := ((l+e)⁻¹-u⁻¹)/((l-3*e)⁻¹-u⁻¹)
  have hGap : 0 < l⁻¹-u⁻¹ := sub_pos.mpr (inv_strictAnti₀ hl hlu)
  have hnum : ContinuousAt (fun e : ℝ => (l+e)⁻¹-u⁻¹) 0 := by
    apply ContinuousAt.sub _ continuousAt_const
    apply (continuousAt_const.add continuousAt_id).inv₀
    simpa using hl.ne'
  have hden : ContinuousAt (fun e : ℝ => (l-3*e)⁻¹-u⁻¹) 0 := by
    apply ContinuousAt.sub _ continuousAt_const
    apply (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).inv₀
    simpa using hl.ne'
  have hθ : ContinuousAt θ 0 := hnum.div hden (by simpa using hGap.ne')
  have h0 : θ 0 = 1 := by simp [θ,hGap.ne']
  have hevent : ∀ᶠ e in 𝓝 (0 : ℝ), γ₀ < θ e :=
    hθ.eventually (Ioi_mem_nhds (h0 ▸ hγ₀))
  obtain ⟨e,he,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := min (l/100) (e/2)
  have hδ : 0 < δ := lt_min (by positivity) (half_pos he)
  have hδl : δ ≤ l/100 := min_le_left _ _
  have hgδ : γ₀ < θ δ := hball (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hδ]
    exact (min_le_right _ _).trans_lt (half_lt_self he))
  let a := l-3*δ
  let b := l-2*δ
  let s := l-δ
  let t := l+δ
  let v := (23/20)*l
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hbs : b < s := by dsimp [b,s]; linarith
  have hst : s ≤ t := by dsimp [s,t]; linarith
  have htu : t < u := by dsimp [t,u]; linarith
  have huv : u < v := by dsimp [u,v]; linarith
  have hvd : v < 3*l := by dsimp [v]; linarith
  have hthin : v^3 < 2*a^3 := by
    have ha97 : (97/100 : ℝ)*l ≤ a := by dsimp [a]; linarith
    calc
      v^3 < 2*((97/100 : ℝ)*l)^3 := by dsimp [v]; nlinarith only [pow_pos hl 3]
      _ ≤ 2*a^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha97 3) (by norm_num)
  obtain ⟨R,C,hR,hC,hI⟩ := exists_parameter_radial_interpolation g p₀ hg hbg hg₀ c
    ha hab hbs hst htu huv hvd hthin
  have hta : t⁻¹ < a⁻¹ := inv_strictAnti₀ ha (hab.trans (hbs.trans_le hst))
  have htu' : u⁻¹ < t⁻¹ := inv_strictAnti₀ (ha.trans_le (hab.le.trans (hbs.le.trans hst))) htu
  have hγ : θ δ < 1 := (div_lt_one (sub_pos.mpr (htu'.trans hta))).mpr (sub_lt_sub_right hta _)
  refine ⟨δ,C,θ δ,hδ,hδl,hC,hgδ,hγ,?_⟩
  filter_upwards [Metric.closedBall_mem_nhds p₀ hR] with p hp
  have hO : ball c (l+δ) ⊆ ball c (3*l) := ball_subset_ball (htu.trans (huv.trans hvd)).le
  exact ⟨(ball_subset_ball hst).trans hO,hO,hI p hp⟩

end CalderonN.FixedTube
