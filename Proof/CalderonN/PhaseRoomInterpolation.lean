module

public import Proof.CalderonN.HarmonicCollarInterpolation
public import Proof.CalderonN.PhaseRooms
public import Proof.CalderonN.CrossProductWeak

import Proof.CalderonN.ConcaveMetricWeight
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open Elliptic Elliptic.PhaseCoordinates

/-- Fixed asymmetric rooms and both interpolation constants work on
one neighborhood of a strict-phase metric in a smooth family. -/
theorem exists_family_phaseRoom_interpolation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {g : P → (MetricField dim)} (hg : ∀ a, SmoothMetric univ (g a))
    (hgm : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => g q.1 q.2 i j))
    (hb : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g q.1) q.2 i j))
    (a₀ : P) {θ : (X dim) → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : (X dim)) (h₀ : θ p = 0)
    (hs : StrictMetricWeightAt (g a₀) θ p) :
    ∃ E : OpenPartialHomeomorph (X dim) (ℝ × (fderiv ℝ θ p).ker), p ∈ E.source ∧
      (∀ x, E x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      ∃ a k : ℝ, 0 < a ∧ 0 < k ∧
        Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a ⊆ E.target ∧
        ∀ κ l ε R : ℝ, 0 < κ → κ ≤ k → 0 < ε → 4*ε < l → 0 < R →
          l+4*ε ≤ a → R ≤ a → κ*(l+4*ε) < 1/4 → 4*ε < κ*l^2 →
          let D := E.symm '' roomD l ε R
          let S := E.symm '' (roomStop l ε R ∪ roomSlat l ε R)
          let O := E.symm '' roomO l ε R
          ∃ (hD : IsOpen D) (hSD : S ⊆ D) (hOD : O ⊆ D),
            ∃ A γ : ℝ, 0 < A ∧ 1/2 < γ ∧ γ < 1 ∧ ∀ a ∈ closedBall a₀ k,
              HarmonicInterpolation hD (smoothMetric_restrict (hg a) (subset_univ D)) hSD hOD A γ := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hs.1 (funext fun i => by simp [coordDeriv,h])
  obtain ⟨E,hEp,hE,b₀,hb₀,hBig₀,hcut⟩ := exists_room_cutoff hθ p h₀ hell
  have hφ : ContDiff ℝ ∞ (fun q : P × (X dim) => θ q.2) := hθ.comp contDiff_snd
  obtain ⟨r,C,τ₀,hr,hC,hτ₀,hCar⟩ :=
    exists_concave_metricCarleman (g := g) (θ := fun _ : P => θ)
      hgm (fun a x => (hg a).2 x (mem_univ x)) hφ a₀ p hs
  obtain ⟨hp0,h0t⟩ := chart_symm_zero E hE (map_zero _) h₀ hEp
  obtain ⟨d,hd,hbox⟩ := exists_box_image_subset_ball E hp0 h0t hr
  let a := min b₀ (d/2)
  have ha : 0 < a := lt_min hb₀ (half_pos hd)
  have haa : a ≤ b₀ := min_le_left _ _
  have hBig : Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a ⊆ E.target :=
    (prod_mono (Icc_subset_Icc (neg_le_neg haa) haa) (closedBall_subset_closedBall haa)).trans hBig₀
  have hball := hbox a ((min_le_right _ _).trans_lt (half_lt_self hd)) hBig
  refine ⟨E,hEp,hE,a,r,ha,hr,hBig,fun κ l ε R hκ hκr hε hεl hR hl haR hκl hε4 => ?_⟩
  let D := E.symm '' roomD l ε R
  let S := E.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let O := E.symm '' roomO l ε R
  let B := E.symm '' transB l ε R
  let H := E.symm '' (transT l ε R ∪ transL l ε R)
  obtain ⟨hD,hO,hS,_,_,_,_,_,hOD,_,hSD,_,_,hB,hBD,hH,hHS,_,hSub⟩ :=
    native_rooms E hBig hε hεl hR hl haR
  have hSD' : S ⊆ D := subset_closure.trans hSD
  have hOD' : O ⊆ D := subset_closure.trans hOD
  refine ⟨hD,hSD',hOD',?_⟩
  obtain ⟨χ,hχ,hχc,hχsupp,hχO,hχgerm⟩ := hcut l ε R hε hεl hR (hl.trans haa) (haR.trans haa)
  have hDbox : (closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a := closedD_subset_big hε hl haR
  have hDt := hDbox.trans hBig
  have hχD : tsupport χ ⊆ D := hχsupp.trans hSub
  have hχB : tsupport χ ⊆ closedBall p r := hχD.trans
    ((image_mono (roomD_subset_closedD.trans hDbox)).trans (hball.trans ball_subset_closedBall))
  obtain ⟨hθB,hθH,hθO⟩ := native_weight_heights E hE hκ hε hεl hR hκl hDt
  have hχtrans (x : (X dim)) (hx : x ∉ B ∪ H) :
      (χ =ᶠ[nhds x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    apply hχgerm x
    simpa only [B,H,image_union,union_assoc] using hx
  have hκsmall : κ*l ≤ 1/4 := by nlinarith [mul_pos hκ hε]
  let ψ (x : (X dim)) := strictHeight κ (θ x)
  have hψ : Continuous ψ := hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  obtain ⟨hgapB,hgapH,hγ₁,hγ₂⟩ := strictExponent_bounds hκ (by linarith) hκsmall hε.le hε4
  have hcarl (u : P) (hu : u ∈ closedBall a₀ r) :=
    hCar u hu κ (by simpa only [abs_of_pos hκ] using hκr)
  obtain ⟨A,hA,hInterp⟩ := exists_family_harmonicInterpolation_of_collarCutoff
    (isCompact_closedBall a₀ r) g hg hb hD hS hO.measurableSet hSD' hOD'
    hB hH hBD hHS (fun a => smoothMetric_restrict (hg a) (subset_univ D)) hχ hχc hχD hχB
    (fun x hx => hχO x (image_mono roomO_subset_closedO hx)) hχtrans hψ
    (sub_pos.mp hgapB) (sub_pos.mp hgapH) hC.le hτ₀ hθB hθH
    (fun x hx => hθO x (image_mono roomO_subset_closedO hx)) hcarl
  exact ⟨A,_,hA,hγ₁,hγ₂,hInterp⟩

/-- Around a strict phase point, the asymmetric source rooms have
interpolation exponents greater than one half for the actual chart
operator. -/
theorem exists_phaseRoom_interpolation {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {θ : (X dim) → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : (X dim)) (h₀ : θ p = 0)
    (hs : StrictMetricWeightAt g θ p) :
    ∃ E : OpenPartialHomeomorph (X dim) (ℝ × (fderiv ℝ θ p).ker), p ∈ E.source ∧
      (∀ x, E x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      ∃ a k : ℝ, 0 < a ∧ 0 < k ∧
        Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a ⊆ E.target ∧
        ∀ κ l ε R : ℝ, 0 < κ → κ ≤ k → 0 < ε → 4*ε < l → 0 < R →
          l+4*ε ≤ a → R ≤ a → κ*(l+4*ε) < 1/4 → 4*ε < κ*l^2 →
          let D := E.symm '' roomD l ε R
          let S := E.symm '' (roomStop l ε R ∪ roomSlat l ε R)
          let O := E.symm '' roomO l ε R
          ∃ (hD : IsOpen D) (hgD : SmoothMetric D g) (hSD : S ⊆ D) (hOD : O ⊆ D),
              ∃ A γ : ℝ, 0 < A ∧ 1/2 < γ ∧ γ < 1 ∧
                HarmonicInterpolation hD hgD hSD hOD A γ := by
  have hgm (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.2 i j) :=
    (contDiffOn_univ.mp (hg.1 i j)).comp contDiff_snd
  have hb (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff g q.2 i j) :=
    (contDiffOn_univ.mp (contDiffOn_divergenceCoeff hg i j)).comp contDiff_snd
  obtain ⟨E,hEp,hE,a,k,ha,hk,hBig,hRooms⟩ := exists_family_phaseRoom_interpolation
    (g := fun _ : ℝ => g) (fun _ => hg) hgm hb 0 hθ p h₀ hs
  refine ⟨E,hEp,hE,a,k,ha,hk,hBig,fun κ l ε R hκ hκk hε hεl hR hl haR hκl hε4 => ?_⟩
  obtain ⟨hD,hSD,hOD,A,γ,hA,hγ,hγ',hI⟩ :=
    hRooms κ l ε R hκ hκk hε hεl hR hl haR hκl hε4
  exact ⟨hD,smoothMetric_restrict hg (subset_univ _),hSD,hOD,A,γ,hA,hγ,hγ',
    hI 0 (mem_closedBall_self hk.le)⟩

end CalderonN
