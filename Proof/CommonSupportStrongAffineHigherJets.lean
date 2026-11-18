import Proof.MixedJetConstantShift
import Proof.CommonSupportOperatorHigherJets
import Proof.LocalCoefficientOperatorCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupport_strong_full_sub_smul_families
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ)
    (hField : ∀ p,aD p = a p-r • a1 p) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
    (∀ t,strongDirichletOperator fixedSobolevCalculus 0 (F t)-
      r • strongDirichletOperator fixedSobolevCalculus 0 (F1 t) = strongDirichletOperator fixedSobolevCalculus 0 (FD t)) ∧
    (∀ t,fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)-
      r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t) = fullCoefficientOperatorL fixedSobolevCalculus 0 (FD t)) := by
  intro F F1 FD
  have hCoeff (t : P) (z : X) : coefficientMatrixField 2 (F t-r • F1 t) z = coefficientMatrixField 2 (FD t) z := by
    have hA := congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a ha S hS hz t)
    have hA1 := congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)
    have hAD := congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 aD haD SD hSD hzD t)
    ext i j
    change coefficientValue 2 ((F t-r • F1 t) i j) z = _
    simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul]
    change coefficientMatrixField 2 (F t) z i j-r*coefficientMatrixField 2 (F1 t) z i j = coefficientMatrixField 2 (FD t) z i j
    rw [hA,hA1,hAD,hField]
    rfl
  constructor
  · intro t
    have h := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (F t-r • F1 t) (FD t) (fun z _ => hCoeff t z)).1
    change (strongCoefficientOperatorL fixedSobolevCalculus 0) (F t-r • F1 t) = _ at h
    rw [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
      (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at h
    exact h
  · intro t
    have h := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (F t-r • F1 t) (FD t) (fun z _ => hCoeff t z)).2
    rw [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
      (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at h
    exact h

theorem commonSupport_affine_remainder_coefficient_germs
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p) (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (x : X) (hx : x ∈ (ballOpens:Set X)) (i j : I) :
    coefficientValue 2 ((commonSupportMatrixFamily 2 a ha S hS hz p-F0-
      r • commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p) i j) =ᶠ[𝓝 x]
        (fun z => (aD (p,z)-(1:Mat)) i j) := by
  filter_upwards [ballOpens.isOpen.mem_nhds hx] with z hzB
  simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul]
  change coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz p) z i j-
    coefficientMatrixField 2 F0 z i j-r*coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p) z i j = _
  rw [coefficientMatrixField_commonSupportMatrixFamily,coefficientMatrixField_commonSupportMatrixFamily,hFlat z hzB,hField]
  change a (p,z) i j-(1:Mat) i j-r*a1 (p,z) i j = (a (p,z) i j-r*a1 (p,z) i j)-(1:Mat) i j
  ring

theorem commonSupport_strong_full_affine_remainder_point_bound
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p) (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ k.val (fun z => (aD (p,z)-(1:Mat)) i j) x‖ ≤ q) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz p
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p
    ‖strongDirichletOperator fixedSobolevCalculus 0 F-strongDirichletOperator fixedSobolevCalculus 0 F0-
      r • strongDirichletOperator fixedSobolevCalculus 0 F1‖ ≤ strongC1OperatorBudget fixedSobolevCalculus*q ∧
    ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F-fullCoefficientOperatorL fixedSobolevCalculus 0 F0-
      r • fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖ ≤ fullC1OperatorBudget fixedSobolevCalculus*q := by
  intro F F1
  let R := F-F0-r • F1
  have hG (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      coefficientValue 2 (R i j) =ᶠ[𝓝 x] (fun z => (aD (p,z)-(1:Mat)) i j) :=
    commonSupport_affine_remainder_coefficient_germs a a1 aD ha ha1 S S1 hS hS1 hz hz1 r hField F0 hFlat p x hx i j
  have hV (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) : |coefficientValue 2 (R i j) x| ≤ q := by
    rw [(hG i j x hx).eq_of_nhds]
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hJets i j ⟨0,by omega⟩ x hx
  have hD (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) : ‖fderiv ℝ (coefficientValue 2 (R i j)) x‖ ≤ q := by
    rw [(hG i j x hx).fderiv_eq]
    simpa only [norm_iteratedFDeriv_one] using hJets i j ⟨1,by omega⟩ x hx
  have hS := norm_strongDirichletOperator_zero_le fixedSobolevCalculus R q hq hV hD
  have hF := norm_fullCoefficientOperator_zero_le fixedSobolevCalculus R q hq hV hD
  change ‖(strongCoefficientOperatorL fixedSobolevCalculus 0) (F-F0-r • F1)‖ ≤ _ at hS
  dsimp only [R] at hF
  rw [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
    (strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
    (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at hS
  rw [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
    (fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
    (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at hF
  exact ⟨hS,hF⟩

/-- All mixed native strong/full Taylor jets, including order zero, depend
    only on the corresponding local mixed jets of the true flat residual. -/
theorem norm_iteratedFDeriv_commonSupport_strong_full_affine_remainder_le
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2) (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ q) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    ‖iteratedFDeriv ℝ n (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)-
      strongDirichletOperator fixedSobolevCalculus 0 F0-r • strongDirichletOperator fixedSobolevCalculus 0 (F1 t)) p‖ ≤
        2*strongC1OperatorBudget fixedSobolevCalculus*q ∧
    ‖iteratedFDeriv ℝ n (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)-
      fullCoefficientOperatorL fixedSobolevCalculus 0 F0-r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)) p‖ ≤
        2*fullC1OperatorBudget fixedSobolevCalculus*q := by
  intro F F1
  have hSB := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  have hFB := fullC1OperatorBudget_nonneg fixedSobolevCalculus
  by_cases hn : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero] at hJets ⊢
    have hPoint := commonSupport_strong_full_affine_remainder_point_bound a a1 aD ha ha1 S S1 hS hS1 hz hz1
      r hField F0 hFlat p q hq hJets
    constructor <;> nlinarith [hPoint.1,hPoint.2]
  · have hn1 : 1 ≤ n := by omega
    let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
    have hMixed (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
        ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => aD (t,z) i j) x) p‖ ≤ q := by
      have he := iteratedFDeriv_parameter_spatial_sub_fixed_pos (fun v => aD v i j)
        (contDiff_pi.mp (contDiff_pi.mp haD i) j) (fun _ : X => (1:Mat) i j) contDiff_const p x n k.val hn1
      rw [← he]
      exact hJets i j k x hx
    have hOps := commonSupport_strong_full_sub_smul_families a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
    have hSFun (t : P) : strongDirichletOperator fixedSobolevCalculus 0 (F t) =
        0+r • strongDirichletOperator fixedSobolevCalculus 0 (F1 t)+strongDirichletOperator fixedSobolevCalculus 0 (FD t) := by
      rw [← hOps.1 t]
      module
    have hFFun (t : P) : fullCoefficientOperatorL fixedSobolevCalculus 0 (F t) =
        0+r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)+fullCoefficientOperatorL fixedSobolevCalculus 0 (FD t) := by
      rw [← hOps.2 t]
      module
    constructor
    · rw [iteratedFDeriv_affine_taylor_family_eq_pos _ _ _ 0 _ r p
        (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 aD haD SD hSD hzD).contDiffAt n hn1 hSFun]
      exact norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus aD haD SD hSD hzD p n q hq hMixed
    · rw [iteratedFDeriv_affine_taylor_family_eq_pos _ _ _ 0 _ r p
        (contDiff_commonSupport_fullCoefficientOperator 0 aD haD SD hSD hzD).contDiffAt n hn1 hFFun]
      exact norm_iteratedFDeriv_commonSupport_fullOperator_zero_le fixedSobolevCalculus aD haD SD hSD hzD p n q hq hMixed

end ShrinkingSpheres
