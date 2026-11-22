module

public import Proof.CalderonN.FixedTube.RadialInterpolation
public import Proof.CalderonN.HarmonicInterpolationChain

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-! The open-and-closed sphere argument is adapted from
`MixedKernelPropagationAndAnnularSeries.lean` at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

/-- Ball propagation: the sphere-step hypothesis `hstep` makes an open reached set
relatively closed in `D`. -/
private theorem closure_inter_subset_of_ball_boundary_step
    {R D : Set (X dim)} (hR : IsOpen R) (hD : IsOpen D)
    (hstep : ∀ c ∈ R, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ball c r ⊆ R → sphere c r ⊆ R) :
    closure R ∩ D ⊆ R := by
  rintro p ⟨hpcl,hpD⟩
  obtain ⟨rD,hrD,hballD⟩ := Metric.isOpen_iff.mp hD p hpD
  let d := rD/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨c,hcp,hcR⟩ := mem_closure_iff.mp hpcl (ball p d) isOpen_ball (mem_ball_self hd)
  have hcpd : dist c p < d := mem_ball.mp hcp
  let A := dist c p+d
  have hA : 0 < A := add_pos_of_nonneg_of_pos dist_nonneg hd
  have hAD : closedBall c A ⊆ D := by
    intro y hy
    apply hballD
    rw [mem_ball]
    have hxy : dist y c ≤ A := mem_closedBall.mp hy
    have ht := dist_triangle y c p
    dsimp [A,d] at hxy hcpd
    linarith
  let F := closedBall c A \ R
  have hF : IsCompact F := (isCompact_closedBall c A).diff hR
  have hFempty : F = ∅ := by
    by_contra hne
    have hFne : F.Nonempty := nonempty_iff_ne_empty.mpr hne
    obtain ⟨x,hx,hmin⟩ := hF.exists_isMinOn hFne (continuous_const.dist continuous_id).continuousOn
    have hxne : c ≠ x := by
      intro heq
      exact hx.2 (heq ▸ hcR)
    let r := dist c x
    have hr : 0 < r := dist_pos.mpr hxne
    have hrA : r ≤ A := by simpa only [r,dist_comm] using mem_closedBall.mp hx.1
    have hbr : ball c r ⊆ R := by
      intro y hy
      by_contra hyR
      have hyd : dist c y < r := by simpa only [dist_comm] using mem_ball.mp hy
      have hyF : y ∈ F := ⟨by rw [mem_closedBall,dist_comm]; exact hyd.le.trans hrA,hyR⟩
      have hle : dist c x ≤ dist c y := hmin hyF
      change r ≤ dist c y at hle
      linarith
    have hcrD : closedBall c r ⊆ D := (closedBall_subset_closedBall hrA).trans hAD
    have hxs : x ∈ sphere c r := by rw [mem_sphere,dist_comm]
    exact hx.2 (hstep c hcR r hr hcrD hbr hxs)
  have hpA : p ∈ closedBall c A := by
    rw [mem_closedBall,dist_comm]
    dsimp [A]
    linarith
  by_contra hpR
  have hpF : p ∈ F := ⟨hpA,hpR⟩
  rw [hFempty] at hpF
  exact hpF

private theorem subset_of_connected_ball_boundary_step {R D : Set (X dim)}
    (hR : IsOpen R) (hD : IsOpen D) (hDc : IsConnected D) (hne : (D ∩ R).Nonempty)
    (hstep : ∀ c ∈ R, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ball c r ⊆ R → sphere c r ⊆ R) :
    D ⊆ R :=
  hDc.isPreconnected.subset_of_closure_inter_subset hR hne
    (closure_inter_subset_of_ball_boundary_step hR hD hstep)

private def reachedSet {P : Type*} [TopologicalSpace P] (p₀ : P)
    {D S : Set (X dim)} (hD : IsOpen D) {g : P → (MetricField dim)}
    (hg : ∀ p, SmoothMetric D (g p)) (hSD : S ⊆ D) : Set (X dim) :=
  {x | ∃ O : Set (X dim), IsOpen O ∧ x ∈ O ∧ ∃ (hOD : O ⊆ D) (C γ : ℝ),
    0 < C ∧ 0 < γ ∧ γ < 1 ∧
      ∀ᶠ p in 𝓝 p₀, HarmonicInterpolation hD (hg p) hSD hOD C γ}

private theorem isOpen_reachedSet {P : Type*} [TopologicalSpace P] (p₀ : P)
    {D S : Set (X dim)} (hD : IsOpen D) {g : P → (MetricField dim)}
    (hg : ∀ p, SmoothMetric D (g p)) (hSD : S ⊆ D) :
    IsOpen (reachedSet p₀ hD hg hSD) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨O,hO,hx,hOD,C,γ,hC,hγ,hγ1,h⟩
  exact ⟨O,fun y hy => ⟨O,hO,hy,hOD,C,γ,hC,hγ,hγ1,h⟩,hO,hx⟩

set_option maxHeartbeats 600000 in
private theorem compact_reached_interpolation {P : Type*} [TopologicalSpace P] (p₀ : P)
    {D S K : Set (X dim)} (hD : IsOpen D) {g : P → (MetricField dim)}
    (hg : ∀ p, SmoothMetric D (g p)) (hSD : S ⊆ D)
    (hK : IsCompact K) (hKD : K ⊆ D) (hKR : K ⊆ reachedSet p₀ hD hg hSD) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ γ < 1 ∧
      ∀ᶠ p in 𝓝 p₀, HarmonicInterpolation hD (hg p) hSD hKD C γ := by
  classical
  have hw (x : K) := hKR x.2
  choose O hO hxO hOD C β hC hβ hβ1 h using hw
  obtain ⟨t,hCover⟩ := hK.elim_finite_subcover O hO
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxO ⟨x,hx⟩⟩)
  let A : Finset ℝ := insert (1/2) (t.image β)
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  let γ := A.min' hA
  have hBounds (s : ℝ) (hs : s ∈ A) : 0 < s ∧ s < 1 := by
    rcases Finset.mem_insert.mp hs with h | h
    · rw [h]
      norm_num
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨hβ i,hβ1 i⟩
  have hγ := hBounds γ (Finset.min'_mem _ _)
  have hle (i : K) (hi : i ∈ t) : γ ≤ β i :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem β hi))
  let Ctot := (∑ i ∈ t, C i) + 1
  have hCsum : 0 ≤ ∑ i ∈ t, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨Ctot,γ,by dsimp [Ctot]; positivity,hγ.1,hγ.2,?_⟩
  have he : ∀ᶠ p in 𝓝 p₀, ∀ i ∈ t, HarmonicInterpolation hD (hg p) hSD (hOD i) (C i) (β i) :=
    (eventually_all_finset t).mpr (fun i _ => h i)
  filter_upwards [he] with p hp q
  let obs := ‖harmonicRestrict hD (hg p) hSD q‖
  let z : ℝ := obs^γ * ‖q‖^(1-γ)
  have hobs : 0 ≤ obs := norm_nonneg _
  have hz : 0 ≤ z := mul_nonneg (Real.rpow_nonneg hobs _) (Real.rpow_nonneg (norm_nonneg q) _)
  have hPart (i : K) (hi : i ∈ t) : ‖harmonicRestrict hD (hg p) (hOD i) q‖ ≤ C i * z := by
    refine (hp i hi q).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (interpolation_product_mono_exponent hobs
      (harmonicRestrict_norm_le hD (hg p) hSD q) hγ.1 (hle i hi)) (hC i).le
  calc
    ‖harmonicRestrict hD (hg p) hKD q‖ ≤ ∑ i ∈ t, ‖harmonicRestrict hD (hg p) (hOD i) q‖ :=
      harmonicRestrict_norm_le_finset_cover t hD (hg p) O (fun i => (hO i).measurableSet) hOD hKD hCover q
    _ ≤ ∑ i ∈ t, C i * z := Finset.sum_le_sum hPart
    _ = (∑ i ∈ t, C i) * z := (Finset.sum_mul _ _ _).symm
    _ ≤ Ctot * z := mul_le_mul_of_nonneg_right (by dsimp [Ctot]; linarith) hz
    _ = _ := by dsimp [z,obs]; ring

set_option maxHeartbeats 650000 in
/-- An exponent uniform near the Euclidean parameter propagates from the
observed open set to any compact target of the connected domain. -/
theorem exists_connected_harmonicInterpolation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (g : P → (MetricField dim)) (p₀ : P) (hg : ∀ p, SmoothMetric univ (g p))
    (hbg : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g z.1) z.2 i j))
    (hg₀ : g p₀ = fun _ => (1 : (Mat dim)))
    {D S K : Set (X dim)} (hD : IsOpen D) (hconn : IsConnected D)
    (hS : IsOpen S) (hSne : S.Nonempty) (hSD : S ⊆ D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ γ < 1 ∧ ∀ᶠ p in 𝓝 p₀,
      HarmonicInterpolation hD (smoothMetric_restrict (hg p) (subset_univ D)) hSD hKD C γ := by
  let hgD (p : P) := smoothMetric_restrict (hg p) (subset_univ D)
  let R := reachedSet p₀ hD hgD hSD
  have hSR : S ⊆ R := by
    intro x hx
    refine ⟨S,hS,hx,hSD,1,1/2,one_pos,by norm_num,by norm_num,?_⟩
    apply Eventually.of_forall
    intro p q
    simpa only [one_mul] using observed_norm_le_interpolation (γ := 1/2)
      (norm_nonneg _) (harmonicRestrict_norm_le hD (hgD p) hSD q) (by norm_num)
  have hne : (D ∩ R).Nonempty := hSne.mono (subset_inter hSD hSR)
  have hStep : ∀ c ∈ R, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ball c r ⊆ R → sphere c r ⊆ R := by
    intro c _ r hr hcr hbr x hx
    obtain ⟨e,he,heD⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open hD hcr
    rw [cthickening_closedBall he.le hr.le] at heD
    let δ := min (r/100) (e/8)
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hδr : δ ≤ r/100 := min_le_left _ _
    have hδe : δ ≤ e/8 := min_le_right _ _
    let a := r-3*δ
    let b := r-2*δ
    let s := r-δ
    let t := r+δ
    let u := r+2*δ
    let v := r+3*δ
    let d := r+4*δ
    have ha : 0 < a := by dsimp [a]; linarith
    have hab : a < b := by dsimp [a,b]; linarith
    have hbs : b < s := by dsimp [b,s]; linarith
    have hst : s ≤ t := by dsimp [s,t]; linarith
    have htu : t < u := by dsimp [t,u]; linarith
    have huv : u < v := by dsimp [u,v]; linarith
    have hvd : v < d := by dsimp [v,d]; linarith
    have hthin : v^3 < 2*a^3 := by
      have hvl : v ≤ (103/100 : ℝ)*r := by dsimp [v]; linarith
      have hal : (97/100 : ℝ)*r ≤ a := by dsimp [a]; linarith
      calc
        v^3 ≤ ((103/100 : ℝ)*r)^3 := pow_le_pow_left₀ (by dsimp [v]; positivity) hvl _
        _ < 2*((97/100 : ℝ)*r)^3 := by nlinarith only [pow_pos hr 3]
        _ ≤ 2*a^3 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hal _) (by norm_num)
    have hdD : ball c d ⊆ D := (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by dsimp [d]; linarith))).trans heD
    have hsc : closedBall c s ⊆ ball c r := closedBall_subset_ball (by dsimp [s]; linarith)
    have hscD : closedBall c s ⊆ D := hsc.trans (ball_subset_closedBall.trans hcr)
    obtain ⟨C₁,α,hC₁,hα,hα1,hFirst⟩ := compact_reached_interpolation p₀ hD hgD hSD
      (isCompact_closedBall c s) hscD (hsc.trans hbr)
    obtain ⟨ρ,C₂,hρ,hC₂,hSecond⟩ := exists_parameter_radial_interpolation g p₀ hg hbg hg₀ c
      ha hab hbs hst htu huv hvd hthin
    let β := (t⁻¹-u⁻¹)/(a⁻¹-u⁻¹)
    have hBO : u⁻¹ < t⁻¹ := inv_strictAnti₀ (ha.trans_le (hab.le.trans (hbs.le.trans hst))) htu
    have hOH : t⁻¹ < a⁻¹ := inv_strictAnti₀ ha (hab.trans (hbs.trans_le hst))
    have hβ : 0 < β := div_pos (sub_pos.mpr hBO) (sub_pos.mpr (hBO.trans hOH))
    have hβ1 : β < 1 := (div_lt_one (sub_pos.mpr (hBO.trans hOH))).mpr (sub_lt_sub_right hOH _)
    have htd : ball c t ⊆ ball c d := ball_subset_ball (htu.trans (huv.trans hvd)).le
    have hsd : ball c s ⊆ ball c d := (ball_subset_ball hst).trans htd
    have hxp : x ∈ ball c t := by
      rw [mem_ball,mem_sphere.mp hx]
      dsimp [t]
      linarith
    refine ⟨ball c t,isOpen_ball,hxp,htd.trans hdD,C₂*C₁^β,α*β,
      mul_pos hC₂ (Real.rpow_pos_of_pos hC₁ _),mul_pos hα hβ,?_ ,?_⟩
    · exact (mul_lt_mul_of_pos_right hα1 hβ).trans_le (by simpa using hβ1.le)
    have hNear : ∀ᶠ p in 𝓝 p₀, p ∈ closedBall p₀ ρ :=
      Metric.closedBall_mem_nhds _ hρ
    filter_upwards [hFirst,hNear] with p hp hpρ
    have hSmall : HarmonicInterpolation hD (hgD p) hSD (hsd.trans hdD) C₁ α := by
      intro q
      exact (harmonicRestrict_norm_mono hD (hgD p) ball_subset_closedBall hscD q).trans (hp q)
    exact HarmonicInterpolation.comp_of_subset hD isOpen_ball (hgD p) hdD hSD hsd htd
      hC₁.le hC₂.le hα hα1 hβ hβ1 hSmall (hSecond p hpρ)
  have hDR : D ⊆ R := subset_of_connected_ball_boundary_step
    (isOpen_reachedSet p₀ hD hgD hSD) hD hconn hne hStep
  exact compact_reached_interpolation p₀ hD hgD hSD hK hKD (hKD.trans hDR)

end CalderonN.FixedTube
