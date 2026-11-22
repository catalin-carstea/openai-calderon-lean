module

public import Proof.CalderonN.ActualWeakAngularRadial
public import Proof.CalderonN.ActualStrongAngularRadial
public import Proof.CalderonN.ActualFiniteRadialMidpoint

import Mathlib.Tactic

/-! Interpolation of the physical angular commutator uses one common
linear family of boundary maps on all finite harmonics. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_angular_radial_midpoint (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∀ i j : Fin dim, ∀ f : HarmonicFiniteCoefficients dim,
        let u := harmonicFiniteSmooth f
        let qθ := harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f
        ∃ b bθ R : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn bθ.1 (sphereRotationDerivative i j u.1) (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          EqOn (negativeBallDivergence a bθ.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z, R.1 z = sphereRotationDerivative i j (fun w => fderiv ℝ b.1 w w) z-
            fderiv ℝ bθ.1 z z-r*fderiv ℝ qθ.1 z z) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η₀,C₀,hη₀,hC₀,hLow⟩ := uniform_actual_weak_angular_radial (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,C₁,hη₁,hC₁,hHigh⟩ := uniform_actual_strong_angular_radial (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,_,_,hη,_,_,hLifts⟩ := uniform_normalized_coefficient_lifts (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix dim 2
  refine ⟨min (min η₀ η₁) η,(C₀+C₁)/2,lt_min (lt_min hη₀ hη₁) hη,by positivity,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  obtain ⟨F,_,hF,_,_,_,lo,hi,hEll⟩ := hLifts F0 hF0 floor hf ε he (hes.trans (min_le_right _ _)) d hd y hy
  let A := coefficientMatrixField 2 F
  have ha : ContDiff ℝ ∞ A := contDiff_coefficientMatrixField 2 F
  have hAa : EqOn A a (ball (0 : X dim) 1) :=
    fun z hz => hF (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)
  have hAg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hAa hw
  have hT (f : HarmonicFiniteCoefficients dim) :
      ∃ b : SmoothData dim, EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
        EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) := by
    obtain ⟨v,hv,hvT,hvH,_⟩ := exists_native_classicalBallPoisson 0 F hEll (harmonicFiniteSmooth f)
    exact ⟨⟨v,hv⟩,hvT,hvH⟩
  choose b hbT hbH using hT
  have hBa (f : HarmonicFiniteCoefficients dim) :
      EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    rw [← negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl]
    exact hbH f hz
  intro i j
  let B := smoothBallAngularDataL i j
  let Kθ := finiteHarmonicRotationL i j
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  have hB (u v : smoothBallDataSubmodule dim) (h : EqOn u.1 v.1 (standardSphere dim)) :
      EqOn (B u).1 (B v).1 (standardSphere dim) :=
    EqOn.sphereRotationDerivative h (smoothBallData_contDiff u) (smoothBallData_contDiff v) i j
  let q := harmonicFiniteDriftVariationSmoothL ellθ
  let D := smoothBallRadialDataL.comp q
  let Z (s : ℝ) (hs : s ≤ 2) :=
    finiteMappedRadialResponseL hn s hs B hB ha hEll b hbT hbH-
      (finiteRadialResponseL hn s hs ha hEll b hbT hbH).comp Kθ-
      r • (smoothBoundarySobolevLinear hn s hs).comp D
  let asS (u : SmoothData dim) : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let Z' (f : HarmonicFiniteCoefficients dim) : smoothBallDataSubmodule dim :=
    B (smoothBallRadialDataL (asS (b f)))-smoothBallRadialDataL (asS (b (Kθ f)))-r • (D f)
  let R (f : HarmonicFiniteCoefficients dim) : SmoothData dim :=
    ⟨(Z' f).1,smoothBallData_contDiff (Z' f)⟩
  have hZ (s : ℝ) (hs : s ≤ 2) (f : HarmonicFiniteCoefficients dim) :
      Z s hs f = smoothBoundarySobolev hn s hs (R f) := by
    rw [show smoothBoundarySobolev hn s hs (R f) = smoothBoundarySobolevLinear hn s hs (Z' f) from
      (smoothBoundarySobolevLinear_apply hn s hs (Z' f)).symm]
    simp only [Z,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      finiteMappedRadialResponseL_apply,finiteRadialResponseL_apply,Z',map_sub,map_smul]
    rfl
  have hR (f : HarmonicFiniteCoefficients dim) (z : X dim) :
      (R f).1 z = sphereRotationDerivative i j (fun w => fderiv ℝ (b f).1 w w) z-
        fderiv ℝ (b (Kθ f)).1 z z-r*fderiv ℝ (harmonicFiniteDriftVariationSmooth ellθ f).1 z z := by
    change sphereRotationDerivative i j (smoothBallRadialDataL (asS (b f))).1 z-
      (smoothBallRadialDataL (asS (b (Kθ f)))).1 z-r*(smoothBallRadialDataL (q f)).1 z = _
    rw [smoothBallRadialDataL_val,smoothBallRadialDataL_val,smoothBallRadialDataL_val,
      harmonicFiniteDriftVariationSmoothL_val]
  have hBt (f : HarmonicFiniteCoefficients dim) :
      EqOn (b (Kθ f)).1 (sphereRotationDerivative i j (harmonicFiniteSmooth f).1) (standardSphere dim) := by
    have h := hbT (Kθ f)
    rwa [harmonicFiniteSmooth_rotation] at h
  have hAny (f : HarmonicFiniteCoefficients dim) (u v E : SmoothData dim)
      (huT : EqOn u.1 (harmonicFiniteSmooth f).1 (standardSphere dim))
      (hvT : EqOn v.1 (sphereRotationDerivative i j (harmonicFiniteSmooth f).1) (standardSphere dim))
      (huH : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
      (hvH : EqOn (negativeBallDivergence a v.1) 0 (ball (0 : X dim) 1))
      (hE : ∀ z, E.1 z = sphereRotationDerivative i j (fun w => fderiv ℝ u.1 w w) z-
        fderiv ℝ v.1 z z-r*fderiv ℝ (harmonicFiniteDriftVariationSmooth ellθ f).1 z z) :
      EqOn (R f).1 E.1 (standardSphere dim) := by
    let u₀ := smoothBallRadialDerivative (b f)
    let u₁ := smoothBallRadialDerivative u
    have hu : EqOn u₀.1 u₁.1 (standardSphere dim) :=
      eqOn_radialDerivative_of_classicalNormalResponses ha hEll hAa (b f) u (hBa f) huH
        (fun z hz => (hbT f hz).trans (huT hz).symm)
    have hv := eqOn_radialDerivative_of_classicalNormalResponses ha hEll hAa (b (Kθ f)) v
      (hBa (Kθ f)) hvH (fun z hz => (hBt f hz).trans (hvT hz).symm)
    have hk := EqOn.sphereRotationDerivative hu u₀.2 u₁.2 i j
    intro z hz
    rw [hR,hE,show sphereRotationDerivative i j (fun w => fderiv ℝ (b f).1 w w) z =
      sphereRotationDerivative i j (fun w => fderiv ℝ u.1 w w) z from hk hz,
      show fderiv ℝ (b (Kθ f)).1 z z = fderiv ℝ v.1 z z from hv hz]
  have h₀ (f : HarmonicFiniteCoefficients dim) :
      ‖Z (-1/2 : ℝ) (by norm_num) f‖ ≤ C₀*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
    obtain ⟨u,v,E,huT,hvT,huH,hvH,hE,hN⟩ := hLow floor hf ε he
      (hes.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy i j f
    rw [hZ,smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) _ _ (hAny f u v E huT hvT huH hvH hE)]
    have he : (-1/2 : ℝ) = -(1/2 : ℝ) := by ring
    rw [smoothBoundarySobolev_order_eq hn he _ (by norm_num)]
    exact hN
  have h₁ (f : HarmonicFiniteCoefficients dim) :
      ‖Z (1/2 : ℝ) (by norm_num) f‖ ≤ C₁*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ := by
    obtain ⟨u,v,E,huT,hvT,huH,hvH,hE,hN⟩ := hHigh floor hf ε he
      (hes.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy i j f
    rw [hZ,smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) _ _ (hAny f u v E huT hvT huH hvH hE)]
    exact hN
  intro f
  refine ⟨b f,b (Kθ f),R f,hbT f,hBt f,hBa f,hBa (Kθ f),hR f,?_⟩
  have hMid : ‖Z 0 (by norm_num) f‖ ≤ ((C₀*r^2+C₁*r^2)/2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    refine norm_finiteSphere_midpoint_le
      (Z (-1/2 : ℝ) (by norm_num)) (Z 0 (by norm_num)) (Z (1/2 : ℝ) (by norm_num))
      ?_ ?_ (C₀*r^2) (C₁*r^2) (by positivity) (by positivity) h₀ h₁ f
    · intro g
      rw [hZ 0,hZ (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn 0 (-1/2 : ℝ) _ _ _ (R g)
    · intro g
      rw [hZ (1/2 : ℝ),hZ (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn (1/2 : ℝ) (-1/2 : ℝ) _ _ _ (R g)
  rw [hZ] at hMid
  exact hMid.trans_eq (by ring)

end CalderonN
