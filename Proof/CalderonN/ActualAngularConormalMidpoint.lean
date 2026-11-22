module

public import Proof.CalderonN.AngularConormalTaylorAlgebra
public import Proof.CalderonN.ActualAngularRadialMidpoint
public import Proof.CalderonN.FiniteDriftRadialOperator

import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! The genuine conormal rotation commutator has a quadratic midpoint
bound. The four terms use the same two physical Dirichlet solutions. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5100000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_angular_conormal_midpoint (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∀ A : X dim → Mat dim, ContDiff ℝ ∞ A → EqOn A a (ball (0 : X dim) (5/4)) →
      ∀ i j : Fin dim, ∀ f : HarmonicFiniteCoefficients dim,
        let u := harmonicFiniteSmooth f
        let ellθ := ell.comp (ballRotationGeneratorL i j)
        let qθ := harmonicFiniteDriftVariationSmooth ellθ f
        ∃ b bθ F : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn bθ.1 (sphereRotationDerivative i j u.1) (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          EqOn (negativeBallDivergence a bθ.1) 0 (ball (0 : X dim) 1) ∧
          EqOn F.1 (fun z => sphereRotationDerivative i j (smoothBallConormal A b.1) z -
            smoothBallConormal A bθ.1 z-r*(ellθ z*fderiv ℝ u.1 z z+fderiv ℝ qθ.1 z z))
            (standardSphere dim) ∧
          ‖smoothSphereLift F.1 F.2‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η₀,B₀,hη₀,hB₀,hR₀⟩ := uniform_actual_finite_radial_midpoint (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηθ,Bθ,hηθ,hBθ,hRθ⟩ := uniform_actual_angular_radial_midpoint (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,C,hηW,hC,hW⟩ := uniform_actual_angular_radial_weights (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηL,P,hηL,hP,hEll⟩ := uniform_actual_radial_weight_remainder (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  let D := ∑ i : Fin dim, ‖radialDriftOperator (axis i)‖
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let B := (1+C)*Bθ+C*(D*C)+C*1+C*(B₀+D*P)
  refine ⟨min (min η₀ ηθ) (min ηW (min ηL 1)),B,
    lt_min (lt_min hη₀ hηθ) (lt_min hηW (lt_min hηL zero_lt_one)),by dsimp [B]; positivity,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  intro A hA hAa i j f
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  let u := harmonicFiniteSmooth f
  let U := smoothBallRadialDerivative u
  let Q := smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ell f)
  let Qθ := smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ellθ f)
  let L := ‖harmonicBoundaryFiniteL 1 f‖
  have h1 := hs.trans (min_le_left _ _)
  have h2 := hs.trans (min_le_right _ _)
  obtain ⟨b₀,R₀,hb₀T,hb₀H,hR₀E,hR₀N⟩ :=
    hR₀ floor hf ε he (h1.trans (min_le_left _ _)) d hd y hy f
  obtain ⟨b,bθ,R,hbT,hbθT,hbH,hbθH,hRE,hRN⟩ :=
    hRθ floor hf ε he (h1.trans (min_le_right _ _)) d hd y hy i j f
  obtain ⟨hPos,W,Wsub,_,hCW,hW₀,hW₁,hWV⟩ :=
    hW floor hf ε he (h2.trans (min_le_left _ _)) d hd y hy A hA hAa
  obtain ⟨hEllθ,V,E,hVEq,hVE,hVN⟩ := hWV i j
  have hEll₀ : ‖ell‖ ≤ P := (hEll floor hf ε he
    (h2.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy).1
  obtain ⟨lo,hi,hAE⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hPos
  have hRad : EqOn (fun z => fderiv ℝ b.1 z z) (fun z => fderiv ℝ b₀.1 z z) (standardSphere dim) :=
    eqOn_radialDerivative_of_classicalNormalResponses hA hAE
      (hAa.mono (ball_subset_ball (by norm_num))) b b₀ hbH hb₀H
      (fun z hz => (hbT hz).trans (hb₀T hz).symm)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hr₁ : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2).trans
      (h2.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let N := smoothBallRadialDerivative b
  let Nθ := smoothBallRadialDerivative bθ
  let A0 : SmoothData dim := ⟨smoothBallConormal A b.1,contDiff_smoothBallConormal hA b⟩
  let Aθ : SmoothData dim := ⟨smoothBallConormal A bθ.1,contDiff_smoothBallConormal hA bθ⟩
  let Δ : SmoothData dim := ⟨fun z => R₀.1 z+r*Q.1 z,R₀.2.add (contDiff_const.mul Q.2)⟩
  have hΔ : EqOn Δ.1 (fun z => N.1 z-U.1 z) (standardSphere dim) := by
    intro z hz
    change R₀.1 z+r*fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z =
      fderiv ℝ b.1 z z-fderiv ℝ u.1 z z
    have hRadZ : fderiv ℝ b.1 z z = fderiv ℝ b₀.1 z z := hRad hz
    have he₀ : R₀.1 z = fderiv ℝ b₀.1 z z-fderiv ℝ u.1 z z-
      r*fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z := hR₀E z
    rw [hRadZ,he₀]
    ring
  have hNormQ (ℓ : X dim →L[ℝ] ℝ) (p : ℝ) (hp : ‖ℓ‖ ≤ p) :
      let q := smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ℓ f)
      ‖smoothSphereLift q.1 q.2‖ ≤ (D*p)*L := by
    dsimp only
    rw [← norm_smoothBoundarySobolev_zero_eq hn]
    exact (norm_first_finite_radial_zero_le hn ℓ f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD) (norm_nonneg _))
  have hΔN : ‖smoothSphereLift Δ.1 Δ.2‖ ≤ (B₀+D*P)*r*L := by
    let H := smoothBoundaryLiftL (dim:=dim) hn
    let x : smoothBallDataSubmodule dim := ⟨R₀.1,R₀.2⟩
    let y : smoothBallDataSubmodule dim := ⟨Q.1,Q.2⟩
    change ‖smoothSphereLift (x+r • y).1 (smoothBallData_contDiff (x+r • y))‖ ≤ _
    rw [← smoothBoundaryLiftL_apply hn,map_add,map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul_of_nonneg hr.le,smoothBoundaryLiftL_apply,smoothBoundaryLiftL_apply]
    change ‖smoothSphereLift R₀.1 R₀.2‖+r*‖smoothSphereLift Q.1 Q.2‖ ≤ _
    have hQ := hNormQ ell P hEll₀
    rw [norm_smoothBoundarySobolev_zero_eq hn R₀] at hR₀N
    have hR₀' : ‖smoothSphereLift R₀.1 R₀.2‖ ≤ B₀*r*L :=
      hR₀N.trans (by dsimp only [L]; gcongr; nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr₁)])
    exact (add_le_add hR₀' (mul_le_mul_of_nonneg_left hQ hr.le)).trans_eq (by ring)
  have hU : ‖smoothSphereLift U.1 U.2‖ ≤ 1*L := by
    rw [← norm_smoothBoundarySobolev_zero_eq hn,one_mul]
    exact norm_flat_finite_radial_zero_le hn f
  rw [norm_smoothBoundarySobolev_zero_eq hn R] at hRN
  obtain ⟨F,hF,hFN⟩ := norm_angular_conormal_remainder_le i j A0 Aθ N Nθ U Qθ W Wsub V E R Δ
    r C (B₀+D*P) Bθ L 1 (D*C) hr.le hr₁ hC (by positivity) hBθ (by positivity) zero_le_one (by positivity)
    ellθ (hCW b) (hCW bθ) hW₀ hVEq hVE (fun z _ => hRE z) hΔ
    (fun z hz => ⟨(hW₁ z (sphere_subset_closedBall hz)).2.2.2.1,
      (hVN z (sphere_subset_closedBall hz)).1,(hVN z (sphere_subset_closedBall hz)).2.2.1⟩)
    hRN hΔN hU (hNormQ ellθ C hEllθ)
  exact ⟨b,bθ,F,hbT,hbθT,hbH,hbθH,hF,hFN⟩

end CalderonN
