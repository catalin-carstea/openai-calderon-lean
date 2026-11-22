module

public import Proof.CalderonN.ActualConormalDegreeForm
public import Proof.CalderonN.SmoothConormalTaylorSymmetry
public import Proof.CalderonN.SmoothDegreeCommutatorCompletion

import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! The quadratic degree form for the actual conormal Taylor remainder
holds for smooth physical data, using the genuine Green adjoints. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5300000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_smooth_conormal_degree_form (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∃ (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A)
        (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f),
        EqOn A a (ball (0 : X dim) (5/4)) ∧
        ∀ u v : SmoothData dim,
          let T (f : SmoothData dim) := (S f).remainder hA r
          let B (f : SmoothData dim) := (S f).degree
          |⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift (B v).1 (B v).2⟫_ℝ-
            ⟪smoothSphereLift (T (B u)).1 (T (B u)).2,smoothSphereLift v.1 v.2⟫_ℝ| ≤
            C*r^2*‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num) u‖*
              ‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num) v‖ := by
  obtain ⟨η,C,hη,hC,hFinite⟩ := uniform_actual_conormal_degree_form (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,_,hηW,_,hWeights⟩ := uniform_actual_angular_radial_weights (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F₀,hF₀⟩ := exists_flatCoefficientMatrix dim 2
  refine ⟨min η ηW,C,lt_min hη hηW,hC,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  obtain ⟨A,b,T₀,τ,hA,hAa,hb,hτ,hPair⟩ :=
    hFinite floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy
  obtain ⟨hPos,_⟩ := hWeights floor hf ε he (hs.trans (min_le_right _ _)) d hd y hy A hA hAa
  obtain ⟨lo,hi,hAE⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hPos
  obtain ⟨F,hFA⟩ := exists_smoothCoefficientMatrix_eqOn hA
  have hPosF (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : (coefficientMatrixField 2 F z).PosDef := by
    rw [hFA (closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) hz)]
    exact hPos z hz
  obtain ⟨lo',hi',hFE⟩ := exists_uniformEllipticOn_fixedBall (coefficientMatrixField 2 F)
    (contDiff_coefficientMatrixField 2 F).continuous hPosF
  let S (u : SmoothData dim) := Classical.choice (exists_conormalTaylorSolutions_of_extension F F₀
    hF₀ (hFA.mono (ball_subset_ball (by norm_num))) hFE ell u)
  let T (u : SmoothData dim) := (S u).remainder hA r
  let B (u : SmoothData dim) := (S u).degree
  have hAg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4) hz)] with w hw
    exact hAa hw
  have hSym (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : (A z).IsSymm :=
    (hPos z (ball_subset_closedBall hz)).isHermitian.isSymm
  let S₀ (f : HarmonicFiniteCoefficients dim) : ConormalTaylorSolutions A ell (harmonicFiniteSmooth f) := {
    actual := b f
    flat := harmonicFiniteSmooth f
    first := harmonicFiniteDriftVariationSmooth ell f
    actualTrace := (hb f).1
    actualEquation := by
      intro z hz
      rw [negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl]
      exact (hb f).2 hz
    flatTrace := fun _ _ => rfl
    flatEquation := fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z
    firstTrace := harmonicFiniteDriftVariationSmooth_trace ell f
    firstEquation := fun z _ => negativeBallDivergence_flat_harmonicFiniteDriftVariation ell f z }
  have hDegree (f : HarmonicFiniteCoefficients dim) :
      EqOn (B (harmonicFiniteSmooth f)).1 (harmonicFiniteSmooth (finiteHarmonicDegreeL f)).1 (standardSphere dim) := by
    refine (conormalTaylorSolutions_degree_eqOn hA hAE (S (harmonicFiniteSmooth f)) (S₀ f)
      (fun _ _ => rfl)).trans ?_
    intro z _
    exact congrFun (harmonicFiniteSmooth_degree_eq_radial f).symm z
  have hRem (u : SmoothData dim) (f : HarmonicFiniteCoefficients dim)
      (hTrace : EqOn u.1 (harmonicFiniteSmooth f).1 (standardSphere dim)) :
      smoothSphereLift (T u).1 (T u).2 = T₀ f := by
    rw [(hτ f).1]
    apply smoothSphereLift_eq_of_eqOn (T u) (τ f)
    refine (conormalTaylorSolutions_remainder_eqOn hA hAE (S u) (S₀ f) hTrace r).trans ?_
    intro z hz
    have hEq := (hτ f).2 hz
    change (τ f).1 z = smoothBallConormal A (b f).1 z-
      (flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z at hEq
    rw [flatRadialDataL_apply,firstConormalDataL_apply] at hEq
    exact hEq.symm
  have hDegLift (f : HarmonicFiniteCoefficients dim) :
      smoothSphereLift (B (harmonicFiniteSmooth f)).1 (B (harmonicFiniteSmooth f)).2 =
        finiteHarmonicSphereL hn (finiteHarmonicDegreeL f) := by
    rw [finiteHarmonicSphereL_apply]
    exact smoothSphereLift_eq_of_eqOn _ _ (hDegree f)
  refine ⟨A,hA,S,hAa,fun u v => ?_⟩
  apply abs_smooth_degree_pair_le_of_finite hn T B
    (fun f g => conormalTaylorSolutions_remainder_symmetric hn hA hSym (S f) (S g) r)
    (fun f g => conormalTaylorSolutions_degree_symmetric (S f) (S g)) (C*r^2)
  intro f g
  dsimp only
  rw [hRem (harmonicFiniteSmooth f) f (fun _ _ => rfl),hDegLift g,
    hRem (B (harmonicFiniteSmooth f)) (finiteHarmonicDegreeL f) (hDegree f),
    ← finiteHarmonicSphereL_apply hn g]
  exact hPair f g

end CalderonN
