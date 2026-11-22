module

public import Proof.CalderonN.ActualConormalSobolevTaylor
public import Proof.CalderonN.SmoothBoundaryMultiplier
public import Proof.CalderonN.SmoothBoundaryLinear

public import Proof.CalderonN.BallRadialDerivative
import Mathlib.Tactic

/-! Bounds on the two low-order radial model terms, from the same
energy-to-boundary pairing as the actual conormal response. -/

public section

noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_halfTrace_dual_of_fixedBallEnergy (hn : 3 ≤ dim)
    (F : FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hF : ‖F‖ ≤ q)
    (f : HarmonicFiniteCoefficients dim) (V : SmoothData dim)
    (hV : ∀ g : HarmonicFiniteCoefficients dim,
      F (smoothSobolev (harmonicFiniteSmooth f)) (smoothSobolev (harmonicFiniteSmooth g)) =
        unitSphereArea dim * ∫ w : ↥(standardSphere dim),
          (harmonicFiniteSmooth g).1 w*V.1 w ∂(sphereProbability dim)) :
    ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) V‖ ≤
      q*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  have hAr := unitSphereArea_pos (dim := dim)
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
    V (q*‖L f‖) (by positivity)
  intro g
  have hf : ‖smoothSobolev (harmonicFiniteSmooth f)‖ ≤ Real.sqrt (unitSphereArea dim)*‖L f‖ :=
    (harmonicFirstOrderLift_finite_smooth f) ▸ norm_harmonicFirstOrderLift_le (L f)
  have hg : ‖smoothSobolev (harmonicFiniteSmooth g)‖ ≤ Real.sqrt (unitSphereArea dim)*‖L g‖ :=
    (harmonicFirstOrderLift_finite_smooth g) ▸ norm_harmonicFirstOrderLift_le (L g)
  have h : ‖F (smoothSobolev (harmonicFiniteSmooth f)) (smoothSobolev (harmonicFiniteSmooth g))‖ ≤
      unitSphereArea dim*(q*‖L f‖*‖L g‖) :=
    (F.le_opNorm₂ _ _).trans (calc
      _ ≤ q*(Real.sqrt (unitSphereArea dim)*‖L f‖)*(Real.sqrt (unitSphereArea dim)*‖L g‖) := by gcongr
      _ = _ := by
        rw [show q*(Real.sqrt (unitSphereArea dim)*‖L f‖)*(Real.sqrt (unitSphereArea dim)*‖L g‖) =
          (Real.sqrt (unitSphereArea dim))^2*(q*‖L f‖*‖L g‖) from by ring,Real.sq_sqrt hAr.le])
  rw [hV g,Real.norm_eq_abs,abs_mul,abs_of_pos hAr] at h
  refine ((mul_le_mul_iff_of_pos_left hAr).mp h).trans_eq' ?_
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

theorem norm_flat_finite_radial_low_le (hn : 3 ≤ dim) (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num)
      (smoothBallRadialDerivative (harmonicFiniteSmooth f))‖ ≤
      (dim : ℝ)^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  let u := harmonicFiniteSmooth f
  let E := fixedBallFlatEnergyL dim
  have hBound : ‖E‖ ≤ (dim : ℝ)^2 := by
    have h := norm_fixedBallSmoothEnergyL_le (dim := dim) (a := fun _ => (1 : Mat dim))
      continuous_const 1 (by norm_num) (fun _ _ i j => by
        classical
        rw [Matrix.one_apply]
        split_ifs <;> norm_num)
    simpa only [E,fixedBallFlatEnergyL,mul_one] using h
  apply norm_halfTrace_dual_of_fixedBallEnergy hn E ((dim : ℝ)^2) (by positivity) hBound f
  intro g
  let v := harmonicFiniteSmooth g
  unfold E fixedBallFlatEnergyL
  rw [fixedBallSmoothEnergyL_apply,energyFormH1_smooth_eq_boundary_flux contDiff_const u v
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z)]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  congr 1
  simpa only [one_smul,one_mul,smoothBallRadialDerivative] using
    inner_smoothBallFlux_scalar (fun _ => 1) u.1 (w : X dim)

theorem norm_first_finite_radial_low_le (hn : 3 ≤ dim) (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num)
      (smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ell f))‖ ≤
      (1+2*Real.sqrt ((dim : ℝ)+3))*(dim : ℝ)^2*‖ell‖*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  let U := smoothBallRadialDerivative u
  let Q := smoothBallRadialDerivative q
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  let e : SmoothData dim := ⟨ell,ell.contDiff⟩
  let R := smoothDataMul e U
  let V : SmoothData dim := ⟨fun z => R.1 z+Q.1 z,R.2.add Q.2⟩
  let A : X dim → Mat dim := fun z => ell z • 1
  let hA : Continuous A := ell.continuous.smul continuous_const
  let F := fixedBallSmoothEnergyL hA
  have hBound : ‖F‖ ≤ (dim : ℝ)^2*‖ell‖ := by
    apply norm_fixedBallSmoothEnergyL_le hA _ (norm_nonneg ell)
    intro z hz i j
    have hzN : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hzA : |ell z| ≤ ‖ell‖ := by
      rw [← Real.norm_eq_abs]
      exact (ell.le_opNorm z).trans (mul_le_of_le_one_right (norm_nonneg ell) hzN)
    have h1 : |(1 : Mat dim) i j| ≤ 1 := by
      classical
      rw [Matrix.one_apply]
      split_ifs <;> norm_num
    change |ell z*(1 : Mat dim) i j| ≤ ‖ell‖
    rw [abs_mul]
    exact (mul_le_mul hzA h1 (abs_nonneg _) (norm_nonneg ell)).trans_eq (mul_one _)
  have hV : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) V‖ ≤ (dim : ℝ)^2*‖ell‖*‖L f‖ := by
    apply norm_halfTrace_dual_of_fixedBallEnergy hn F _ (by positivity) hBound f V
    intro g
    unfold F
    rw [fixedBallSmoothEnergyL_apply]
    exact affineEnergy_harmonicFinite_eq_firstConormal ell f g
  have hR : ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) R‖ ≤
      (2*Real.sqrt ((dim : ℝ)+3))*‖ell‖*((dim : ℝ)^2*‖L f‖) := by
    refine (norm_smoothBoundarySobolev_mul_negHalf_le hn e U (norm_nonneg ell) ?_ ?_).trans ?_
    · intro z hz
      have hzN : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      change |ell z| ≤ ‖ell‖
      rw [← Real.norm_eq_abs]
      exact (ell.le_opNorm z).trans (mul_le_of_le_one_right (norm_nonneg ell) hzN)
    · intro z hz
      change ‖gradient (⇑ell) z‖ ≤ _
      rw [gradient,LinearIsometryEquiv.norm_map,ContinuousLinearMap.fderiv]
    · exact mul_le_mul_of_nonneg_left (norm_flat_finite_radial_low_le hn f) (by positivity)
  let B := smoothBoundarySobolevLinear hn (-(1/2 : ℝ)) (by norm_num)
  let Q' : smoothBallDataSubmodule dim := ⟨Q.1,Q.2⟩
  let R' : smoothBallDataSubmodule dim := ⟨R.1,R.2⟩
  have hV' : ‖B (R'+Q')‖ ≤ (dim : ℝ)^2*‖ell‖*‖L f‖ := hV
  have hR' : ‖B R'‖ ≤ (2*Real.sqrt ((dim : ℝ)+3))*‖ell‖*((dim : ℝ)^2*‖L f‖) := hR
  change ‖B Q'‖ ≤ _
  have hq : B Q' = B (R'+Q')-B R' := by rw [map_add,add_sub_cancel_left]
  rw [hq]
  exact ((norm_sub_le _ _).trans (add_le_add hV' hR')).trans_eq (by ring)

end CalderonN
