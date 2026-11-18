import Proof.ParallelScalarFirstDefectSquare
import Proof.ParallelScalarFirstSymmetricExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

theorem firstFormalAdjointCore_balanced_density
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    metricDensity d.γ y • sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (P.firstFormalAdjointCore WF W U y)=
      -(∑ b : I,P.firstAdjointBalancedDensityRow WF U b y) := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hRow (b : I) : metricDensity d.γ y • sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCoreRow WF W U b y)=-P.firstAdjointBalancedDensityRow WF U b y := by
    have hActual := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
      (P.firstFormalAdjointCoreRow_density WF W U b (metricDensity_pos hg hK hy).ne')
    have hBalanced := P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF W U hU b
      (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b) hy
    simpa only [map_smul,map_neg,sphereSobolevInclusionL_trans_apply,hBalanced] using hActual
  simp only [PhysicalPrincipalData.firstFormalAdjointCore,map_sum,Finset.smul_sum,hRow,Finset.sum_neg_distrib]

def scalarFirstDefectDensity {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (_W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ)
    (scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y)
    (P.firstAdjointBalancedDensityRow WF U b y))

def scalarFirstDefectComplexDensity {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  scalarFirstDefectDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    scalarFirstDefectDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

theorem scalarFirstDefectDensity_eq_weak_pair
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y) :
    scalarFirstDefectDensity P WF W U y=-2*metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
      (scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y)
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.firstFormalAdjointCore WF W U y)) := by
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  have hGraph := firstFormalAdjointCore_balanced_density hY hΩ hSub hd hK P WF W U hU hy
  have hPair := congrArg (fun z => sphereSobolevDualPairing (1/2:ℝ) F z) hGraph
  simp only [sphereSobolevDualPairing,inner_sum,inner_neg_right,real_inner_smul_right] at hPair
  change 2*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) F (P.firstAdjointBalancedDensityRow WF U b y))=_
  dsimp only [sphereSobolevDualPairing] at hPair ⊢
  linarith only [hPair]

theorem scalarFirstDefectDensity_eq_inner
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) {y : X} (hy : y ∈ Y) :
    scalarFirstDefectDensity P WF W U y=-2*metricDensity d.γ y*
      ⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ)
        (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y,
        P.firstFormalAdjointCore WF W U y⟫_ℝ := by
  rw [scalarFirstDefectDensity_eq_weak_pair hY hΩ hSub hd hK P WF W U hU.contDiffOn hy,
    OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing.sphereSobolevDualPairing_zero_inclusion
      (1/2:ℝ) (by norm_num),scalarFiveHalfDefectSection_inclusion d _ _ U hU y]

theorem scalarFirstDefectDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (scalarFirstDefectDensity P WF W U) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hU20 (x : X) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by simp only [fiveHalfToTwoSection,hU0 x hx,map_zero]
  have hDomain := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) (fun x hx => (metricDensity_pos hg hK hx).ne')
    (scalarPrincipalMatrix d.γ d.g₂ d.radius) (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK)
    (fiveHalfToTwoSection U) hU2 S hS.isClosed hSY hU20
  have hFLp : MemLp (scalarCovariantAdjointDefectSection d (metricDensity d.γ)
      (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U)) 2 (volume.restrict Y) :=
    hDomain.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hDomain.2)
  have hALp := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY hU0
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK) 2
  have hPair := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hFLp hALp
    (fun x _ hx => hDomain.2 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  apply (hPair.const_mul (-2)).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  rw [scalarFirstDefectDensity_eq_inner hY hΩ hSub hd hK P WF W U hU hx]
  ring

theorem abs_scalarFirstDefectDensity_le
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    |scalarFirstDefectDensity P WF W U y| ≤ metricDensity d.γ y*(
      ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y‖^2+
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.firstFormalAdjointCore WF W U y)‖^2) := by
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  let V := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.firstFormalAdjointCore WF W U y)
  let μ := metricDensity d.γ y
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hEq : scalarFirstDefectDensity P WF W U y=-2*μ*sphereSobolevDualPairing (1/2:ℝ) F V := by
    exact scalarFirstDefectDensity_eq_weak_pair hY hΩ hSub hd hK P WF W U hU hy
  rw [hEq]
  change |-2*μ*sphereSobolevDualPairing (1/2:ℝ) F V| ≤ μ*(‖F‖^2+‖V‖^2)
  rw [abs_mul,abs_mul,abs_of_nonneg hμ]
  rw [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hNorm := abs_sphereSobolevDualPairing_le (1/2:ℝ) F V
  have hSq : 2*‖F‖*‖V‖ ≤ ‖F‖^2+‖V‖^2 := by nlinarith only [sq_nonneg (‖F‖-‖V‖)]
  calc
    _ ≤ 2*μ*(‖F‖*‖V‖) := mul_le_mul_of_nonneg_left hNorm (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hSq hμ]

end ShrinkingSpheres.ParallelEnergy
