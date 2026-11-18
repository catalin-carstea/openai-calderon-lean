import Proof.ActualSmoothMidpointRadialFamily
import Proof.CommonSupportRadialAdjointRegularity
import Proof.UniformConormalOneData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- Genuine smooth forward and physical-adjoint radial families for every
    admitted profile. Their physical pairing uses the same full radial map. -/
theorem uniform_actual_smooth_radial_pair {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R Y ∧ ContDiffOn ℝ ∞ A Y ∧
        ∀ y ∈ Y,RealizesActualMidpointRadialError d y (R y) ∧
          ∀ u v,⟪(R y+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
            ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A y v⟫_ℝ := by
  classical
  obtain ⟨ηR,hηR,hSmoothR⟩ := uniform_actual_smooth_midpoint_radial_family hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,hηP,hLocalP⟩ := uniform_actual_normal_local_poisson_family hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,P,Q,CN2,F0,hηN,hP,hQ,hCN2,hF0,hConormal⟩ :=
    uniform_actual_conormal_one_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηR (min ηP ηN),lt_min hηR (lt_min hηP hηN),?_⟩
  intro floor hf ε hε hSmall d hd
  have hSmallR := hSmall.trans (min_le_left _ _)
  have hSmallP := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallN := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨R,hSmooth,hRealizes⟩ := hSmoothR floor hf ε hε hSmallR d hd
  let D : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun y => R y+sphereSobolevDegreeL
  have hD : ContDiffOn ℝ ∞ D Y := hSmooth.add contDiffOn_const
  have hLocal (y : X) (hy : y ∈ Y) :
      ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        ∃ A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ A V ∧
          ∀ p ∈ V,∀ u v,⟪D p u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
            ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A p v⟫_ℝ := by
    have hHere := hLocalP floor hf ε hε hSmallP d hd y hy d.g₁ (by simp)
    obtain ⟨a,ha,S,hS,hz,V,hV,hyV,hVY,hRep,hStrong,hPoisson,hHigh⟩ := hHere
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    have hAt (p : X) (hp : p ∈ V) :
        ∃ N : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          D p = conormalRadialL (F p) N ∧
          (∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet (F p)) w.val) ∧
          ∀ u v,⟪N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
            ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ := by
      have hC := hConormal floor hf ε hε hSmallN d hd p (hVY hp)
      dsimp only at hC
      obtain ⟨G,G1,e,ha1,N,hRepG,hRepG1,hInvG,hInv0,hUE,hV1,hD1,hOne,hN⟩ := hC
      have hG (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) : coefficientMatrixField 2 G z =
          principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap p (d.radius p)) z := by
        ext i j
        exact (hRepG z hzBall i j).eq_of_nhds
      have hF (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) : coefficientMatrixField 2 (F p) z =
          principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap p (d.radius p)) z := by
        simp only [F,coefficientMatrixField_commonSupportMatrixFamily]
        exact (hRep p hp z hzBall).eq_of_nhds
      have hFG (w : UnitSphere) : coefficientMatrixField 2 (F p) w.val = coefficientMatrixField 2 G w.val := by
        have hw : w.val ∈ Metric.closedBall (0:X) 2 :=
          Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
        exact (hF w.val hw).trans (hG w.val hw).symm
      have hPosG (w : UnitSphere) : 0 < (boundaryNormalCoefficientData G).1 w.val :=
        boundaryNormalCoefficientData_pos G _ _ hUE w
      have hPosF (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet (F p)) w.val := by
        rw [normalCoefficientJet_value_congr_sphere (F p) G hFG w,coefficientValue_normalCoefficientJet]
        exact hPosG w
      have hEqG : D p = conormalRadialL G N := by
        apply continuousLinearMap_eq_of_high_restriction
        intro f
        exact ((hRealizes p (hVY hp)).full_high d p (R p) G
          (fun z hzBall => hG z (unitBall_subset_closedBall_two hzBall)) f).trans
            (conormalRadialL_high e.coefficient_bound e.coercive G N
              (fun z hzBall => hG z (unitBall_subset_closedBall_two hzBall)) hInvG hPosG hN.weak_compatible f).symm
      exact ⟨N,hEqG.trans (conormalRadialL_congr_sphere (F p) G N hFG).symm,hPosF,hN.symmetric⟩
    let A := fun p => radialAdjointFromResponseL (F p) (D p)
    have hInv (p : X) (hp : p ∈ V) : (oneBoundaryCoefficientMulL (normalCoefficientJet (F p))).IsInvertible := by
      obtain ⟨N,hEq,hPos,hSym⟩ := hAt p hp
      exact oneBoundaryCoefficientMulL_isInvertible_of_pos _ hPos
    refine ⟨V,hV,hyV,hVY,A,contDiffOn_commonSupport_radialAdjointFromResponse a ha S hS hz D V (hD.mono hVY) hInv,?_⟩
    intro p hp
    obtain ⟨N,hEq,hPos,hSym⟩ := hAt p hp
    exact radialAdjointFromResponseL_pairing (F p) (D p) N hEq hPos hSym
  have hPoint (y : X) (hy : y ∈ Y) :
      ∃ A : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∀ u v,
        ⟪D y u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A v⟫_ℝ := by
    obtain ⟨V,hV,hyV,hVY,A,hA,hPair⟩ := hLocal y hy
    exact ⟨A y,hPair y hyV⟩
  let A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun y =>
    if hy : y ∈ Y then Classical.choose (hPoint y hy) else 0
  have hPair (y : X) (hy : y ∈ Y) : ∀ u v,
      ⟪D y u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A y v⟫_ℝ := by
    dsimp only [A]
    rw [dite_eq_left hy]
    exact Classical.choose_spec (hPoint y hy)
  have hA : ContDiffOn ℝ ∞ A Y := by
    intro y hy
    obtain ⟨V,hV,hyV,hVY,T,hT,hTPair⟩ := hLocal y hy
    have hEq : A =ᶠ[𝓝 y] T := by
      filter_upwards [hV.mem_nhds hyV] with p hp
      exact radial_physical_adjoint_unique (D p) (A p) (T p) (hPair p (hVY hp)) (hTPair p hp)
    exact ((hT.contDiffAt (hV.mem_nhds hyV)).congr_of_eventuallyEq hEq).contDiffWithinAt
  exact ⟨R,A,hSmooth,hA,fun y hy => ⟨hRealizes y hy,hPair y hy⟩⟩

end ShrinkingSpheres
