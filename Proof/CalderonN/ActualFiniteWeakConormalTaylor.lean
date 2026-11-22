module

public import Proof.CalderonN.NativeWeakHarmonicResponse
public import Proof.CalderonN.NormalizedCoefficientLifts
public import Proof.CalderonN.WeakConormalTaylorBound

import Proof.CalderonN.BallRegularity.UniformStrongInverse
import Mathlib.Tactic

/-! Weak endpoint of the actual first-metric conormal Taylor estimate,
using the same coefficient and flat finite harmonic lifts as the strong
radial endpoint. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem energyFormH1_of_eqOn_coefficient
    {a b : X dim → Mat dim} (h : EqOn a b (ball (0 : X dim) 1)) (u v : FixedBallH1 dim) :
    energyFormH1 a 0 0 u v = energyFormH1 b 0 0 u v := by
  rw [energyFormH1_def,energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with z hz
  rw [h hz]

omit [Nontrivial (Fin dim)] in
private theorem abs_coefficientMatrixField_entry_le (F : SmoothCoefficientMatrix dim 2)
    (z : X dim) (i j : Fin dim) : |coefficientMatrixField 2 F z i j| ≤ ‖F‖ := by
  have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 0 (by omega) z
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
  exact h.trans ((norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i))

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem coefficientMatrixField_sub_smul_entry (F F0 F1 : SmoothCoefficientMatrix dim 2)
    (r : ℝ) (z : X dim) (i j : Fin dim) :
    coefficientMatrixField 2 (F-F0-r • F1) z i j =
      coefficientMatrixField 2 F z i j-coefficientMatrixField 2 F0 z i j-
        r*coefficientMatrixField 2 F1 z i j := by
  unfold coefficientMatrixField coefficientValue
  rfl

/-- Weak testing with finite harmonic data bounds the actual flux Taylor
remainder at (H^{1/2}	o H^{-1/2}), uniformly in the two truncations. -/
theorem uniform_actual_finite_weak_conormal_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let a1 (z : X dim) := firstDensityCenterLinear d y z • (1 : Mat dim)
      ∃ aExt : X dim → Mat dim, ContDiff ℝ ∞ aExt ∧ EqOn aExt a (ball (0 : X dim) (5/4)) ∧
      ∀ f : HarmonicFiniteCoefficients dim, ∃ b : SmoothData dim,
        EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
        EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
        ‖smoothSobolev b-smoothSobolev (harmonicFiniteSmooth f)‖ ≤
          B*r*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ ∧
        ∀ g : HarmonicFiniteCoefficients dim,
          let u := harmonicFiniteSmooth f
          let v := harmonicFiniteSmooth g
          let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
          |(unitSphereArea dim * ∫ w : ↥(standardSphere dim), v.1 w *
              ⟪(w : X dim), smoothBallFlux a b.1 w⟫_ℝ ∂(sphereProbability dim)) -
            energyFormH1 (fun _ => (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) -
            r*energyFormH1 a1 0 0 (smoothSobolev u) (smoothSobolev v)| ≤
            B*r^2*‖L f‖*‖L g‖ := by
  obtain ⟨η,P,Q,hη,hP,hQ,hLift⟩ := uniform_normalized_coefficient_lifts (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F0,hF0,_,_,_,_,_⟩ := exists_uniform_strongDirichlet_neighborhood dim 0
  let G := (dim : ℝ)^2*(P+Q)
  let D := (dim : ℝ)^2*Q
  let τ := min η (min 1 ((1/10)/(G+1)))
  let B₀ := (G*(10*G)+D)*unitSphereArea dim
  let B₁ := (10*G)*Real.sqrt (unitSphereArea dim)
  let B := B₀+B₁
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB₀ : 0 ≤ B₀ := mul_nonneg (by positivity)
    (unitSphereArea_pos (dim := dim)).le
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁]; positivity
  refine ⟨τ,B,lt_min hη (lt_min zero_lt_one (by positivity)),add_nonneg hB₀ hB₁,?_⟩
  intro floor hf ε hε hετ d hd y hy
  dsimp only
  obtain ⟨F,F1,hF,hF1,hN1,hNR,lo,hi,hEll⟩ :=
    hLift F0 hF0 floor hf ε hε (hετ.trans (min_le_left _ _)) d hd y hy
  let r := d.radius y
  let a := coefficientMatrixField 2 F
  let a1 := coefficientMatrixField 2 F1
  let A : X dim → Mat dim := fun z => firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let A1 : X dim → Mat dim := fun z => firstDensityCenterLinear d y z • 1
  let ha := (contDiff_coefficientMatrixField 2 F).continuous
  let ha1 := (contDiff_coefficientMatrixField 2 F1).continuous
  let E := fixedBallSmoothEnergyL ha
  let E0 := fixedBallFlatEnergyL dim
  let E1 := fixedBallSmoothEnergyL ha1
  let j := fixedBallZeroInclusionL dim
  let P0 := harmonicFirstOrderLift dim
  let P' := weakDirichletPoissonL j E (isCoercive_fixedBallSmoothEnergy ha hEll) P0
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans
    (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hrε.trans (hετ.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmall : G*r ≤ 1/10 := by
    have he := hrε.trans (hετ.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h := (le_div_iff₀ (by positivity : 0 < G+1)).mp he
    nlinarith only [h,hr]
  have hR : ‖E-E0-r • E1‖ ≤ D*r^2 := by
    have hEntry (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) (i j : Fin dim) :
        |((a-(fun _ : X dim => (1 : Mat dim)))-r • a1) z i j| ≤ Q*r^2 := by
      have h0 := hF0 z (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) (ball_subset_closedBall hz))
      have h := (abs_coefficientMatrixField_entry_le (F-F0-r • F1) z i j).trans hNR
      rw [coefficientMatrixField_sub_smul_entry,h0] at h
      exact h
    have ha0 : Continuous (fun _ : X dim => (1 : Mat dim)) := continuous_const
    have h := norm_fixedBallSmoothEnergyL_le ((ha.sub ha0).sub (ha1.const_smul r))
      (Q*r^2) (by positivity) hEntry
    rw [fixedBallSmoothEnergyL_sub (ha.sub ha0) (ha1.const_smul r),
      fixedBallSmoothEnergyL_sub ha ha0,fixedBallSmoothEnergyL_smul ha1 r] at h
    exact h.trans_eq (by dsimp [D]; ring)
  have hE1 : ‖E1‖ ≤ (dim : ℝ)^2*P :=
    norm_fixedBallSmoothEnergyL_le ha1 P hP (fun z _ i j => (abs_coefficientMatrixField_entry_le F1 z i j).trans hN1)
  have hE : ‖E-E0‖ ≤ G*r := by
    have he : E-E0 = (E-E0-r • E1)+r • E1 := by abel
    rw [he]
    calc
      _ ≤ ‖E-E0-r • E1‖+‖r • E1‖ := norm_add_le _ _
      _ ≤ D*r^2+r*((dim : ℝ)^2*P) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact add_le_add hR (mul_le_mul_of_nonneg_left hE1 hr.le)
      _ ≤ G*r := by
        have h := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ D*r by positivity)
        dsimp only [G,D] at h ⊢
        nlinarith only [h]
  have hCoer (v : FixedBallH1Zero dim) : (1/10 : ℝ)*‖v‖*‖v‖ ≤ E (j v) (j v) := by
    have hFlat : (1/5 : ℝ)*‖v‖*‖v‖ ≤ E0 (j v) (j v) :=
      fixedBallSmoothEnergy_zero_coercive continuous_const
        (uniformlyEllipticOn_const_one_one (n := Fin dim) (fixedBallOpens dim : Set (X dim))) v
    have hjv : ‖j v‖ = ‖v‖ := rfl
    have hDiff : ‖(E-E0) (j v) (j v)‖ ≤ (1/10 : ℝ)*‖v‖*‖v‖ := by
      rw [← hjv]
      exact ((E-E0).le_opNorm₂ _ _).trans (by gcongr; exact hE.trans hSmall)
    simp only [sub_apply,Real.norm_eq_abs] at hDiff
    linarith only [hFlat,(abs_le.mp hDiff).1]
  have hW := norm_weakDirichletPoissonL_sub_le j (norm_fixedBallZeroInclusionL_le dim) E E0
    (isCoercive_fixedBallSmoothEnergy ha hEll) P0 fixedBallFlatEnergyL_harmonicFirstOrderLift_zero
    (1/10 : ℝ) (by norm_num) hCoer
  have hP' : ‖P'-P0‖ ≤ (10*G)*‖P0‖*r := by
    norm_num at hW
    exact hW.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 10))
      (norm_nonneg P0)).trans_eq (by ring))
  have hP0 : ‖P0‖ ≤ Real.sqrt (unitSphereArea dim) :=
    ContinuousLinearMap.opNorm_le_bound P0 (Real.sqrt_nonneg _) norm_harmonicFirstOrderLift_le
  have hFlat : E0.bilinearComp (P'-P0) P0 = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro g
    rw [ContinuousLinearMap.bilinearComp_apply, zero_apply, zero_apply]
    change E0 ((weakDirichletPoissonL j E (isCoercive_fixedBallSmoothEnergy ha hEll) P0-P0) f) (P0 g) = 0
    rw [weakDirichletPoissonL_sub,ContinuousLinearMap.comp_apply]
    exact fixedBallFlatEnergyL_harmonicFirstOrderLift_zero_left _ _
  let R := E.bilinearComp P' P0-E0.bilinearComp P0 P0-r • E1.bilinearComp P0 P0
  have hR' : ‖R‖ ≤ B*r^2 := by
    have h := norm_weakConormal_energy_remainder_le E E0 E1 P' P0 hFlat r G (10*G) D
      hr.le hG (by positivity) hD hE hP' hR
    apply h.trans
    apply le_trans _ (mul_le_mul_of_nonneg_right (show B₀ ≤ B from le_add_of_nonneg_right hB₁) (sq_nonneg _))
    dsimp only [B₀]
    have hM : ‖P0‖^2 ≤ unitSphereArea dim :=
      (pow_le_pow_left₀ (norm_nonneg _) hP0 2).trans_eq (Real.sq_sqrt (unitSphereArea_pos (dim := dim)).le)
    gcongr
  refine ⟨a,contDiff_coefficientMatrixField 2 F,hF,?_⟩
  intro f
  obtain ⟨b,hbT,hbH,hbP⟩ := weakPoissonL_eq_native_classical_finite F hEll f
  have hAB : EqOn a A (ball (0 : X dim) (5/4)) := hF
  have hBV : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    have hGerm : a =ᶠ[𝓝 z] A := by
      filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)]
        with w hw using hAB hw
    rw [← negativeBallDivergence_congr_germ hGerm (EventuallyEq.rfl (f := b.1))]
    exact hbH hz
  refine ⟨b,hbT,hBV,?_,?_⟩
  · let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
    rw [← hbP,← harmonicFirstOrderLift_finite_smooth f]
    change ‖(P'-P0) (L f)‖ ≤ B*r*‖L f‖
    apply ((P'-P0).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply hP'.trans
    calc
      _ ≤ B₁*r := by
        dsimp only [B₁]
        gcongr
      _ ≤ B*r := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀) hr.le
  intro g
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  let u := harmonicFiniteSmooth f
  let v := harmonicFiniteSmooth g
  have hFlux : (unitSphereArea dim * ∫ w : ↥(standardSphere dim), v.1 w *
      ⟪(w : X dim), smoothBallFlux A b.1 w⟫_ℝ ∂(sphereProbability dim)) =
      E (P' (L f)) (P0 (L g)) := by
    change P' (L f) = smoothSobolev b at hbP
    rw [hbP,show P0 (L g) = smoothSobolev v from harmonicFirstOrderLift_finite_smooth g,
      fixedBallSmoothEnergyL_apply,energyFormH1_smooth_eq_boundary_flux (contDiff_coefficientMatrixField 2 F) b v hbH]
    congr 1
    apply integral_congr_ae
    filter_upwards with w
    have hw : (w : X dim) ∈ ball (0 : X dim) (5/4) :=
      closedBall_subset_ball (by norm_num : (1 : ℝ) < 5/4) (sphere_subset_closedBall w.2)
    have he : smoothBallFlux A b.1 w = smoothBallFlux a b.1 w := by
      ext i
      simp only [smoothBallFlux_apply,hAB hw]
    rw [he]
  have hFlux1 : energyFormH1 A1 0 0 (smoothSobolev u) (smoothSobolev v) =
      E1 (P0 (L f)) (P0 (L g)) := by
    rw [show P0 (L f) = smoothSobolev u from harmonicFirstOrderLift_finite_smooth f,
      show P0 (L g) = smoothSobolev v from harmonicFirstOrderLift_finite_smooth g,fixedBallSmoothEnergyL_apply]
    exact energyFormH1_of_eqOn_coefficient (fun z hz => (hF1 (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)).symm) _ _
  change |_ - energyFormH1 (fun _ => (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) -
    r*energyFormH1 A1 0 0 (smoothSobolev u) (smoothSobolev v)| ≤ B*r^2*‖L f‖*‖L g‖
  rw [hFlux,hFlux1,← harmonicFirstOrderLift_finite_smooth f,← harmonicFirstOrderLift_finite_smooth g]
  have h : ‖R (L f) (L g)‖ ≤ B*r^2*‖L f‖*‖L g‖ :=
    (R.le_opNorm₂ (L f) (L g)).trans (by gcongr)
  simpa only [R,E0,P0,sub_apply,ContinuousLinearMap.bilinearComp_apply,
    smul_apply,smul_eq_mul,fixedBallFlatEnergyL,fixedBallSmoothEnergyL_apply,Real.norm_eq_abs]
    using h

end CalderonN
