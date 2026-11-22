module

public import Proof.CalderonN.ActualFiniteWeakConormalTaylor
public import Proof.CalderonN.PolynomialConormalFirstVariation
public import Proof.CalderonN.SmoothBoundarySobolev

import Proof.CalderonN.BallRadialDerivative
import Mathlib.Tactic

/-! The weak conormal estimate in the actual negative half-order sphere
norm, after identifying both Taylor terms as boundary functions. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothConormal (a : X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (b : SmoothData dim) : SmoothData dim :=
  ⟨fun z => ⟪z,smoothBallFlux a b.1 z⟫_ℝ, ContDiff.inner ℝ contDiff_id (contDiff_smoothBallFlux ha b)⟩

private theorem sphere_integrable_of_continuous (u : X dim → ℝ) (hu : Continuous u) :
    Integrable (fun w : ↥(standardSphere dim) => u w) (sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  have h := (hu.comp continuous_subtype_val).continuousOn.integrableOn_compact
    (μ := sphereProbability dim) (isCompact_univ : IsCompact (univ : Set ↥(standardSphere dim)))
  simpa only [IntegrableOn,Measure.restrict_univ,Function.comp_def] using h

/-- Uniform negative half-order control of the genuine normalized conormal
remainder, with the classical radial first variation explicitly subtracted. -/
theorem uniform_actual_conormal_sobolev_taylor (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ f : HarmonicFiniteCoefficients dim,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        let u := harmonicFiniteSmooth f
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b E : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          EqOn E.1 (fun z => ⟪z,smoothBallFlux a b.1 z⟫_ℝ - fderiv ℝ u.1 z z -
            r*(ell z*fderiv ℝ u.1 z z+fderiv ℝ q.1 z z)) (standardSphere dim) ∧
          ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) E‖ ≤
            B*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  obtain ⟨η,B,hη,hB,hT⟩ := uniform_actual_finite_weak_conormal_taylor (Y := Y) (by omega : 2 ≤ dim)
    hΩ hm K ρ c₀ M Cj hK hρ
  let σ := unitSphereArea dim
  have hσ : 0 < σ := unitSphereArea_pos
  refine ⟨η,B/σ,hη,div_nonneg hB hσ.le,?_⟩
  intro floor hf ε hε hεη d hd y hy f
  obtain ⟨a,ha,hA,h⟩ := hT floor hf ε hε hεη d hd y hy
  obtain ⟨b,hbT,hbH,_,hWeak⟩ := h f
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  let C := smoothConormal a ha b
  let U := smoothBallRadialDerivative u
  let Q := smoothBallRadialDerivative q
  let V : SmoothData dim := ⟨fun z => ell z*U.1 z+Q.1 z,(ell.contDiff.mul U.2).add Q.2⟩
  let E : SmoothData dim := ⟨fun z => C.1 z-U.1 z-r*V.1 z,(C.2.sub U.2).sub (contDiff_const.mul V.2)⟩
  have haSphere (z : X dim) (hz : z ∈ standardSphere dim) :
      smoothBallFlux a b.1 z =
        smoothBallFlux (fun z => firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)) b.1 z := by
    have hz' := closedBall_subset_ball (by norm_num : (1 : ℝ) < 5/4) (sphere_subset_closedBall hz)
    have hEq := hA hz'
    ext i
    simp only [smoothBallFlux_apply,hEq,r]
  refine ⟨b,E,hbT,hbH,fun z hz => ?_,?_⟩
  · change C.1 z-U.1 z-r*V.1 z = _
    rw [show C.1 z = ⟪z,smoothBallFlux a b.1 z⟫_ℝ from rfl,haSphere z hz]
    rfl
  · let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
    apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
      E (B/σ*r^2*‖L f‖) (by positivity)
    intro g
    let v := harmonicFiniteSmooth g
    have hEnergy0 : energyFormH1 (fun _ => (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) =
        σ*∫ w : ↥(standardSphere dim), v.1 w*U.1 w ∂(sphereProbability dim) := by
      rw [energyFormH1_smooth_eq_boundary_flux contDiff_const u v
        (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z)]
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      congr 1
      simpa only [one_smul,one_mul,U,smoothBallRadialDerivative] using inner_smoothBallFlux_scalar (fun _ => 1) u.1 (w : X dim)
    have hEnergy1 : energyFormH1 (fun z => ell z • (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) =
        σ*∫ w : ↥(standardSphere dim), v.1 w*V.1 w ∂(sphereProbability dim) :=
      affineEnergy_harmonicFinite_eq_firstConormal ell f g
    have hEnergyA :
        (∫ w : ↥(standardSphere dim), v.1 w *
          ⟪(w : X dim), smoothBallFlux (fun z => firstNormalVelocityCoefficient d y
            (r • frameVector d.frame y z)) b.1 w⟫_ℝ ∂(sphereProbability dim)) =
        ∫ w : ↥(standardSphere dim), v.1 w*C.1 w ∂(sphereProbability dim) := by
      apply integral_congr_ae
      filter_upwards with w
      rw [← haSphere w w.2]
      rfl
    have hSplit :
        (∫ w : ↥(standardSphere dim), E.1 w*v.1 w ∂(sphereProbability dim)) =
        (∫ w : ↥(standardSphere dim), v.1 w*C.1 w ∂(sphereProbability dim)) -
        (∫ w : ↥(standardSphere dim), v.1 w*U.1 w ∂(sphereProbability dim)) -
        r*(∫ w : ↥(standardSphere dim), v.1 w*V.1 w ∂(sphereProbability dim)) := by
      have hc : Integrable (fun w : ↥(standardSphere dim) => v.1 w*C.1 w) (sphereProbability dim) :=
        sphere_integrable_of_continuous _ (v.2.continuous.mul C.2.continuous)
      have hu : Integrable (fun w : ↥(standardSphere dim) => v.1 w*U.1 w) (sphereProbability dim) :=
        sphere_integrable_of_continuous _ (v.2.continuous.mul U.2.continuous)
      have hv : Integrable (fun w : ↥(standardSphere dim) => v.1 w*V.1 w) (sphereProbability dim) :=
        sphere_integrable_of_continuous _ (v.2.continuous.mul V.2.continuous)
      have hPoint (z : X dim) : E.1 z*v.1 z =
          (v.1 z*C.1 z-v.1 z*U.1 z)-r*(v.1 z*V.1 z) := by
        change (C.1 z-U.1 z-r*V.1 z)*v.1 z = _
        ring
      simp_rw [hPoint]
      have h1 := integral_sub (hc.sub hu) (hv.const_mul r)
      have h2 := integral_sub hc hu
      simp only [Pi.sub_apply] at h1 h2
      rw [h1,h2,integral_const_mul]
    have hUg := hWeak g
    change |σ * (∫ w : ↥(standardSphere dim), v.1 w *
        ⟪(w : X dim), smoothBallFlux (fun z => firstNormalVelocityCoefficient d y
          (r • frameVector d.frame y z)) b.1 w⟫_ℝ ∂(sphereProbability dim)) -
        energyFormH1 (fun _ => (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) -
        r*energyFormH1 (fun z => ell z • (1 : Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v)| ≤
        B*r^2*‖L f‖*‖L g‖ at hUg
    rw [hEnergyA,hEnergy0,hEnergy1] at hUg
    have hI : σ*(∫ w : ↥(standardSphere dim), E.1 w*v.1 w ∂(sphereProbability dim)) =
        σ*(∫ w : ↥(standardSphere dim), v.1 w*C.1 w ∂(sphereProbability dim)) -
          σ*(∫ w : ↥(standardSphere dim), v.1 w*U.1 w ∂(sphereProbability dim)) -
          r*(σ*(∫ w : ↥(standardSphere dim), v.1 w*V.1 w ∂(sphereProbability dim))) := by
      rw [hSplit]
      ring
    rw [← hI,abs_mul,abs_of_pos hσ,mul_comm σ] at hUg
    apply (le_div_iff₀ hσ).mpr at hUg
    change _ ≤ B/σ*r^2*‖L f‖*‖L g‖
    exact hUg.trans_eq (by ring)

end CalderonN
