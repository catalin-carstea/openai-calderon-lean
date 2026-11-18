import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.NormalizedMidpointRadialRealization
import Proof.NormalizedCoefficientBoundaryData
import Proof.MidpointRadialAdjointNative
import Proof.RadialConormalReconstruction
import Proof.ActualHighRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}

def radialL (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  s.response.response ((y,frameVectorLinear d.frame y),0)+sphereSobolevDegreeL

def radialAdjointL (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialAdjointFromResponseL
    (commonSupportMatrixFamily 2 s.coefficients.a s.coefficients.smooth s.coefficients.support
      s.coefficients.compact s.coefficients.supported ((y,frameVectorLinear d.frame y),0)) s.radialL

theorem realizesActualMidpointRadialError
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y) :
    RealizesActualMidpointRadialError d y (s.response.response ((y,frameVectorLinear d.frame y),0)) := by
  obtain ⟨hRep,_hRep1⟩ := s.coefficients.actual_point_germs hΩ hd.1 hK (hd.2.1.center_mem hy) le_rfl
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) :
      coefficientMatrixField 2 (commonSupportMatrixFamily 2 s.coefficients.a s.coefficients.smooth
        s.coefficients.support s.coefficients.compact s.coefficients.supported ((y,frameVectorLinear d.frame y),0)) z =
      normalizedFirstNormalCoefficient d y z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  exact realizesActualMidpointRadialError_of_normalized_restriction d y _ _ hField s.point.strong
    (s.response.highRestriction _ s.response.pointMem)

theorem radial_pairing_of_pullback_elliptic
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y)
    (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP
      (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))) :
    ∀ u v,⟪s.radialL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.radialAdjointL v⟫_ℝ := by
  let q := s.coefficients
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p0
  obtain ⟨hRep,_hRep1⟩ := q.actual_point_germs hΩ hd.1 hK (hd.2.1.center_mem hy) le_rfl
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  obtain ⟨hPos,_hOne,hs⟩ := normalized_coefficient_boundary_data d y F KP hKP hEll hField
  have hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible := by
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact s.point.normal
  have hsRaw : ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(q.a (p0,z)).IsSymm := by
    simpa only [F,coefficientMatrixField_commonSupportMatrixFamily] using hs
  exact midpoint_radialAdjointFromResponse_pairing (commonSupportEnergyMemLp q.a q.smooth p0) s.point.coercive hsRaw F
    (fun z _ => by dsimp only [F];rw [coefficientMatrixField_commonSupportMatrixFamily]) s.point.strong hNormal hPos
    (s.response.response p0) (s.response.highRestriction _ s.response.pointMem)

end NativeRelativeHorizontalTaylorData

/-- The SAME packet with horizontal estimates is the actual physical radial
    response and its true probability-sphere adjoint on all realized data. -/
theorem uniform_native_relative_physical_radial_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CM CQ CI CW : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CM ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
        (∀ u v,⟪s.radialL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.radialAdjointL v⟫_ℝ) ∧
        ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
        ∀ f : SphereSobolev (3/2:ℝ),
        (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
          u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (s.radialL (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
            fun w : UnitSphere => radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u := by
  obtain ⟨ηD,CF,CA,CM,CQ,CI,CW,F0,hηD,hηD1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hData⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηP,CP,hηP,_hCP,hPhysical⟩ := uniform_physical_high_radial_endpoint (Y:=Y) hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  refine ⟨min ηD (min ηE ηP),CF,CA,CM,CQ,CI,CW,F0,lt_min hηD (lt_min hηE hηP),
    (min_le_left _ _).trans hηD1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨s⟩ := hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hEll := hElliptic floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  refine ⟨s,s.radial_pairing_of_pullback_elliptic hΩ hd (zero_lt_one.trans_le hK) hy (4*K^2) hKP hEll,?_⟩
  obtain ⟨F,hRep,_hInv,hValue⟩ := hPhysical floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hR := s.realizesActualMidpointRadialError hΩ hd (zero_lt_one.trans_le hK) hy
  intro u hu f hBoundary
  have hh := hR.full_high d y (s.response.response ((y,frameVectorLinear d.frame y),0)) F hField f
  have hEq := congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm hh
  rw [LinearIsometryEquiv.symm_apply_apply] at hEq
  exact hEq.symm ▸ (hValue u hu f hBoundary).1

end ShrinkingSpheres
