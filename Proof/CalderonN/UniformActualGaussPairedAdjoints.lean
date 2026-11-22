module

public import Proof.CalderonN.ActualGaussPairedAdjoint
public import Proof.CalderonN.ActualPhysicalCoefficientGerm
public import Proof.CalderonN.ActualPhysicalVelocityGerm

import Proof.CalderonN.NormalizedCoefficientRemainderC2
import Mathlib.Tactic

/-! The actual Gauss factors and their transposes act on the supported
trace space for the same canonical frames and small radii. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_pairedAdjoints (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
        (hA : SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily D i))
        (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y),
        ∃ T,PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
          (smoothSupportedTraceFiberAction hY (actualGaussFiberFamily D i) hA) T := by
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨ηA,hηA,hCoeff⟩ := uniform_actual_physicalCoefficient_germ hn₂ hY hΩ hYc hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηV,hηV,hVel⟩ := uniform_actual_physicalScaledVelocity_smooth hY hΩ hYc hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,_,hηP,_,hPos⟩ := uniform_normalized_coefficient_remainder_C2 (Y:=Y) hn₂ hΩ hm
    K ρ c₀ M Cj hK hρ 1 (by norm_num)
  refine ⟨min ηA (min ηV ηP),lt_min hηA (lt_min hηV hηP),?_⟩
  intro floor hf ε he hs d hd hF D i hA μ hμ
  let C (x z : X dim) := firstNormalVelocityCoefficient d x (d.radius x • frameVector d.frame x z)
  have hLoc : ∀ y ∈ Y, ∃ (V : Set (X dim)) (a : X dim × X dim → Mat dim) (J : Set (X dim)),
      IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ a ∧ IsCompact J ∧
      (∀ x z,z ∉ J → a (x,z) = 0) ∧
      ∀ x ∈ V,∀ hx : x ∈ Y,EqOn (fun z => a (x,z)) (D x hx).coefficient (closedBall (0:X dim) 1) := by
    intro y hy
    obtain ⟨V,a,J,hV,hyV,hVY,ha,hJ,hSupp,hReal⟩ := hCoeff floor hf ε he
      (hs.trans (min_le_left _ _)) d hd hF y hy
    refine ⟨V,a,J,hV,hyV,hVY,ha,hJ,hSupp,?_⟩
    intro x hx hxY
    have hEq : EqOn (fun z => a (x,z)) (D x hxY).coefficient (ball (0:X dim) 1) :=
      ((hReal x hx).mono ball_subset_closedBall).trans (D x hxY).coefficientEq.symm
    rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
    exact hEq.closure (ha.continuous.comp (continuous_const.prodMk continuous_id))
      (D x hxY).smoothCoefficient.continuous
  have hPositive (x : X dim) (hx : x ∈ Y) (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
      ((D x hx).coefficient z).PosDef := by
    obtain ⟨V,a,_,_,hxV,_,ha,_,_,hReal⟩ := hCoeff floor hf ε he (hs.trans (min_le_left _ _)) d hd hF x hx
    have hEq : EqOn (fun z => a (x,z)) (D x hx).coefficient (ball (0:X dim) 1) :=
      ((hReal x hxV).mono ball_subset_closedBall).trans (D x hx).coefficientEq.symm
    have hClosed : EqOn (fun z => a (x,z)) (D x hx).coefficient (closedBall (0:X dim) 1) := by
      rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
      exact hEq.closure (ha.continuous.comp (continuous_const.prodMk continuous_id))
        (D x hx).smoothCoefficient.continuous
    have hZ : (D x hx).coefficient z = C x z := (hClosed hz).symm.trans (hReal x hxV hz)
    rw [hZ]
    exact (hPos floor hf ε he (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd x hx z hz).2.2.2.2
  have hSym (x : X dim) (hx : x ∈ Y) (z : X dim) (hz : z ∈ ball (0:X dim) 1) :
      ((D x hx).coefficient z).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (hPositive x hx z (ball_subset_closedBall hz)).isHermitian
  have hC := actualGaussConormalFamily_regular hY D (fun x hx => by
    obtain ⟨V,a,J,hV,hxV,hVY,ha,hJ,hSupp,hEq⟩ := hLoc x hx
    exact ⟨V,a,J,hV,hxV,hVY,ha,hJ,hSupp,fun y hy hyY => (hEq y hy hyY).mono ball_subset_closedBall⟩)
  have hW := actualReciprocalSphereMultiplier_regular hY D (fun x hx => by
    obtain ⟨V,a,_,hV,hxV,hVY,ha,_,_,hEq⟩ := hLoc x hx
    exact ⟨V,a,hV,hxV,hVY,ha,hEq⟩)
    (fun x hx z hz => hPositive x hx z (sphere_subset_closedBall hz))
  have hVS := hVel floor hf ε he (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hF i
  obtain ⟨hV,hM⟩ := actualVelocitySphereMultipliers_regular hY D i (actualPhysicalScaledVelocity d i)
    hVS (fun x hx z hz => (D x hx).velocityEq i hz)
  have h := pairedAdjoint_actualSupportedGauss hn hY μ hμ D i hA hC hSym hW hV hM
    hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  exact ⟨_,h⟩

end CalderonN
