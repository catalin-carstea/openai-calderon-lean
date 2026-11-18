import Proof.CommonSupportMultiplierDerivative
import Proof.ClosedLocalZeroMultiplier
import Proof.AngleSpatialDerivative
import Proof.Archive.CollaboratorFixedSobolevCalculusOct17

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The actual compact parameter generator determines both low spatial
jets of the closed coefficient derivative. Higher cutoff jets are irrelevant. -/
theorem commonSupportClosedCoefficient_deriv_low_jets
    (r : ℕ) (hr : 1 ≤ r) (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g)
    (S : Set X) (hS : IsCompact S) (hz : ∀ t z,z ∉ S → g (t,z) = 0)
    (b : X → ℝ) (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    let D := deriv (commonSupportClosedCoefficientFamily r g hg S hS hz) 0
    ∀ z : X,
      D.val ⟨0,Nat.zero_lt_succ _⟩ z = iteratedFDeriv ℝ 0 b z ∧
      D.val ⟨1,by omega⟩ z = iteratedFDeriv ℝ 1 b z := by
  dsimp only
  let F := commonSupportClosedCoefficientFamily r g hg S hS hz
  have hF := (contDiff_commonSupportClosedCoefficientFamily r g hg S hS hz).differentiable (by simp) (0:ℝ)
  intro z
  constructor
  · let C := (continuousMultilinearCurryFin0 ℝ X ℝ).symm
    have hEval := (closedCoefficientJetEvaluationL r ⟨0,Nat.zero_lt_succ _⟩ z).hasFDerivAt.comp_hasDerivAt (0:ℝ) hF.hasDerivAt
    have hOther := C.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hSlice z)
    have hFun : (fun t => closedCoefficientJetEvaluationL r ⟨0,Nat.zero_lt_succ _⟩ z (F t)) =
        fun t => C (g (t,z)) := rfl
    change HasDerivAt (fun t => closedCoefficientJetEvaluationL r ⟨0,Nat.zero_lt_succ _⟩ z (F t)) _ 0 at hEval
    rw [hFun] at hEval
    exact hEval.unique hOther
  · let C := (continuousMultilinearCurryFin1 ℝ X ℝ).symm
    have hEval := (closedCoefficientJetEvaluationL r ⟨1,by omega⟩ z).hasFDerivAt.comp_hasDerivAt (0:ℝ) hF.hasDerivAt
    have hOther := C.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (hasDerivAt_spatial_fderiv_of_angle_generator g hg b hSlice z)
    have hFun : (fun t => closedCoefficientJetEvaluationL r ⟨1,by omega⟩ z (F t)) =
        fun t => C (fderiv ℝ (fun w => g (t,w)) z) := by
      funext t
      change iteratedFDeriv ℝ 1 (fun w => g (t,w)) z = C (fderiv ℝ (fun w => g (t,w)) z)
      ext v
      simp only [iteratedFDeriv_one_apply]
      rfl
    change HasDerivAt (fun t => closedCoefficientJetEvaluationL r ⟨1,by omega⟩ z (F t)) _ 0 at hEval
    rw [hFun] at hEval
    have h := hEval.unique hOther
    have hC : C (fderiv ℝ b z) = iteratedFDeriv ℝ 1 b z := by
      ext v
      simp only [iteratedFDeriv_one_apply]
      rfl
    exact h.trans hC

/-- Exact derivative of the genuine completed H1 multiplier, as the
multiplier of the SAME compact smooth coefficient generator. -/
theorem hasDerivAt_commonSupport_bulkMultiplier_one
    (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → g (t,z) = 0)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    HasDerivAt (fun t => coefficientMultiplier fixedSobolevCalculus 1
      (commonSupportCoefficientFamily 2 g hg S hS hz t))
      (coefficientMultiplier fixedSobolevCalculus 1 (compactCoefficient 2 b hb (HasCompactSupport.intro hS hzb))) 0 := by
  let F := commonSupportClosedCoefficientFamily 2 g hg S hS hz
  let D := deriv F 0
  let G := compactCoefficient 2 b hb (HasCompactSupport.intro hS hzb)
  have hF := (contDiff_commonSupportClosedCoefficientFamily 2 g hg S hS hz).differentiable (by simp) (0:ℝ)
  have hLow := commonSupportClosedCoefficient_deriv_low_jets 2 (by norm_num) g hg S hS hz b hSlice
  have hG (j : Fin 3) (z : X) : G.val j z = iteratedFDeriv ℝ j.val b z := by
    rw [coefficientJet_eq_iteratedFDeriv]
    dsimp only [G]
    rw [coefficientValue_compactCoefficient]
  have hDiff : closedCoefficientMultiplierL fixedSobolevCalculus 1 (D-smoothCoefficientClosureInclusionL 2 G) = 0 := by
    have hNorm : ‖closedCoefficientMultiplierL fixedSobolevCalculus 1 (D-smoothCoefficientClosureInclusionL 2 G)‖ ≤ 4*0 := by
      apply norm_closedCoefficientMultiplier_one_le_of_local_jets fixedSobolevCalculus _ 0 le_rfl
      · intro z
        change ‖D.val ⟨0,Nat.zero_lt_succ _⟩ z-G.val ⟨0,Nat.zero_lt_succ _⟩ z‖ ≤ 0
        rw [(hLow z).1,hG]
        simp
      · intro z
        change ‖D.val ⟨1,Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ z-G.val ⟨1,Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ z‖ ≤ 0
        rw [(hLow z).2,hG]
        simp
    exact norm_le_zero_iff.mp (by simpa only [mul_zero] using hNorm)
  rw [map_sub,sub_eq_zero] at hDiff
  have hDerivative := (closedCoefficientMultiplierL fixedSobolevCalculus 1).hasFDerivAt.comp_hasDerivAt (0:ℝ) hF.hasDerivAt
  have hFun : (fun t => coefficientMultiplier fixedSobolevCalculus 1 (commonSupportCoefficientFamily 2 g hg S hS hz t)) =
      fun t => closedCoefficientMultiplierL fixedSobolevCalculus 1 (F t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth fixedSobolevCalculus 1 _).symm
  rw [hFun]
  have hEq : closedCoefficientMultiplierL fixedSobolevCalculus 1 D = coefficientMultiplier fixedSobolevCalculus 1 G :=
    hDiff.trans (closedCoefficientMultiplierL_eq_on_smooth fixedSobolevCalculus 1 G)
  exact hEq ▸ hDerivative

/-- The corresponding exact L2 multiplier derivative needs only the
zeroth generator jet; it uses the same actual compact coefficient. -/
theorem hasDerivAt_commonSupport_bulkMultiplier_zero
    (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → g (t,z) = 0)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    HasDerivAt (fun t => coefficientMultiplier fixedSobolevCalculus 0
      (commonSupportCoefficientFamily 1 g hg S hS hz t))
      (coefficientMultiplier fixedSobolevCalculus 0 (compactCoefficient 1 b hb (HasCompactSupport.intro hS hzb))) 0 := by
  let F := commonSupportClosedCoefficientFamily 1 g hg S hS hz
  let D := deriv F 0
  let G := compactCoefficient 1 b hb (HasCompactSupport.intro hS hzb)
  have hF := (contDiff_commonSupportClosedCoefficientFamily 1 g hg S hS hz).differentiable (by simp) (0:ℝ)
  have hLow := commonSupportClosedCoefficient_deriv_low_jets 1 (by norm_num) g hg S hS hz b hSlice
  have hDiff : closedCoefficientMultiplierL fixedSobolevCalculus 0 (D-smoothCoefficientClosureInclusionL 1 G) = 0 := by
    apply norm_le_zero_iff.mp
    apply norm_closedCoefficientMultiplier_zero_le_of_local_jet fixedSobolevCalculus _ 0 le_rfl
    intro z
    change ‖D.val ⟨0,Nat.zero_lt_succ _⟩ z-G.val ⟨0,Nat.zero_lt_succ _⟩ z‖ ≤ 0
    rw [(hLow z).1,coefficientJet_eq_iteratedFDeriv]
    dsimp only [G]
    rw [coefficientValue_compactCoefficient]
    simp
  rw [map_sub,sub_eq_zero] at hDiff
  have hDerivative := (closedCoefficientMultiplierL fixedSobolevCalculus 0).hasFDerivAt.comp_hasDerivAt (0:ℝ) hF.hasDerivAt
  have hFun : (fun t => coefficientMultiplier fixedSobolevCalculus 0 (commonSupportCoefficientFamily 1 g hg S hS hz t)) =
      fun t => closedCoefficientMultiplierL fixedSobolevCalculus 0 (F t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth fixedSobolevCalculus 0 _).symm
  rw [hFun]
  have hEq : closedCoefficientMultiplierL fixedSobolevCalculus 0 D = coefficientMultiplier fixedSobolevCalculus 0 G :=
    hDiff.trans (closedCoefficientMultiplierL_eq_on_smooth fixedSobolevCalculus 0 G)
  exact hEq ▸ hDerivative

end ShrinkingSpheres
