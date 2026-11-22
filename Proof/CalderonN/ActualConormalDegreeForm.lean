module

public import Proof.CalderonN.ActualAngularConormalMidpoint
public import Proof.CalderonN.FiniteConormalTaylorOperators

import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! The spectral degree form is the one of the actual normalized
conormal remainder on every finite harmonic datum. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise Topology
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_conormal_degree_form (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∃ (A : X dim → Mat dim) (b : HarmonicFiniteCoefficients dim → SmoothData dim)
        (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
        (τ : HarmonicFiniteCoefficients dim → SmoothData dim),
        ContDiff ℝ ∞ A ∧ EqOn A a (ball (0 : X dim) (5/4)) ∧
        (∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
          EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1)) ∧
        (∀ f,T f = smoothSphereLift (τ f).1 (τ f).2 ∧
          EqOn (τ f).1 (fun z => smoothBallConormal A (b f).1 z -
            (flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z) (standardSphere dim)) ∧
        ∀ f g,
          |⟪T f,finiteHarmonicSphereL hn (finiteHarmonicDegreeL g)⟫_ℝ-
            ⟪T (finiteHarmonicDegreeL f),finiteHarmonicSphereL hn g⟫_ℝ| ≤
            B*r^2*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖ := by
  obtain ⟨η₀,_,hη₀,_,hRad⟩ := uniform_actual_finite_radial_midpoint (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,Bθ,hηA,hBθ,hAngular⟩ :=
    uniform_actual_angular_conormal_midpoint (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,_,hηW,_,hWeights⟩ := uniform_actual_angular_radial_weights (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,_,hηC,_,hCoeff⟩ := uniform_actual_weak_angular_conormal (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min (min η₀ ηA) (min ηW ηC),(dim:ℝ)^4*(Bθ+Bθ),
    lt_min (lt_min hη₀ hηA) (lt_min hηW hηC),by positivity,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  have hSmall₁ := hs.trans (min_le_left _ _)
  have hSmall₂ := hs.trans (min_le_right _ _)
  obtain ⟨A,hA,hAa,_⟩ := hCoeff floor hf ε he (hSmall₂.trans (min_le_right _ _)) d hd y hy
  obtain ⟨hPos,W,_,_,hW,_,_,_⟩ := hWeights floor hf ε he (hSmall₂.trans (min_le_left _ _))
    d hd y hy A hA hAa
  obtain ⟨lo,hi,hEll⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hPos
  have hResp (f : HarmonicFiniteCoefficients dim) :
      ∃ b : SmoothData dim, EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
        EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) := by
    obtain ⟨b,_,hbT,hbH,_,_⟩ := hRad floor hf ε he (hSmall₁.trans (min_le_left _ _)) d hd y hy f
    exact ⟨b,hbT,hbH⟩
  choose b hbT hbH using hResp
  have hAg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4) hz)] with w hw
    exact hAa hw
  have hbHA (f : HarmonicFiniteCoefficients dim) :
      EqOn (negativeBallDivergence A (b f).1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    rw [negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl]
    exact hbH f hz
  have hSym (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : (A z).IsSymm :=
    (hPos z (ball_subset_closedBall hz)).isHermitian.isSymm
  obtain ⟨T,P,τ,hτ,hTS,hP,hTE,hPE⟩ :=
    exists_finiteConormalTaylorOperators hn hA hEll hSym b hbT hbHA W hW ell r
  have hMatch (f : HarmonicFiniteCoefficients dim) (u : SmoothData dim)
      (huT : EqOn u.1 (harmonicFiniteSmooth f).1 (standardSphere dim))
      (huH : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1)) :
      EqOn (smoothBallConormal A (b f).1) (smoothBallConormal A u.1) (standardSphere dim) := by
    have hRad := eqOn_radialDerivative_of_classicalNormalResponses hA hEll
      (hAa.mono (ball_subset_ball (by norm_num))) (b f) u (hbH f) huH
      (fun z hz => (hbT f hz).trans (huT hz).symm)
    intro z hz
    rw [hW (b f) hz,hW u hz]
    change W.1 z*fderiv ℝ (b f).1 z z = W.1 z*fderiv ℝ u.1 z z
    exact congrArg (W.1 z * ·) (hRad hz)
  have hPN (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      ‖P ij f‖ ≤ (Bθ*r^2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    obtain ⟨v,vθ,F,hvT,hvθT,hvH,hvθH,hFE,hFN⟩ :=
      hAngular floor hf ε he (hSmall₁.trans (min_le_right _ _)) d hd y hy A hA hAa ij.1 ij.2 f
    have hv := hMatch f v hvT hvH
    have hvθ := hMatch (finiteHarmonicRotationL ij.1 ij.2 f) vθ
      (by rw [harmonicFiniteSmooth_rotation]; exact hvθT) hvθH
    have hV := EqOn.sphereRotationDerivative hv (contDiff_smoothBallConormal hA (b f))
      (contDiff_smoothBallConormal hA v) ij.1 ij.2
    rw [hPE ij f F ?_]
    · exact hFN
    · intro z hz
      change F.1 z = sphereRotationDerivative ij.1 ij.2 (smoothBallConormal A (b f).1) z -
        smoothBallConormal A (b (finiteHarmonicRotationL ij.1 ij.2 f)).1 z -
        r*(firstConormalDataL (ell.comp (ballRotationGeneratorL ij.1 ij.2)) f).1 z
      rw [hV hz,hvθ hz,firstConormalDataL_apply]
      exact hFE hz
  refine ⟨A,b,T,τ,hA,hAa,fun f => ⟨hbT f,hbH f⟩,fun f => ⟨hτ f,hTE f⟩,?_⟩
  intro f g
  have hh := abs_finite_smooth_degree_pair_le hn T τ hτ hTS P hP (Bθ*r^2) (by positivity) hPN f g
  exact hh.trans_eq (by ring)

end CalderonN
