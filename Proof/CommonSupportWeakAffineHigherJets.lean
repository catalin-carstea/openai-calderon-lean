import Proof.MixedJetConstantShift
import Proof.ZeroEnergyAffineRemainderBound
import Proof.PositiveAffineFamilyJets
import Proof.CommonSupportWeakEnergyHigherJets
import Proof.AffineWeakEnergyFamilyIdentity
import Proof.WeakPoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  TauCeti.PDE.energyFormH1L TauCeti.PDE.energyFormH1L0

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupport_weak_affine_remainder_point_bound
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ x ∈ (ballOpens:Set X),|(aD (p,x)-(1:Mat)) i j| ≤ q) :
    ‖commonSupportFullWeakEnergy a ha p-TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-
      r • commonSupportFullWeakEnergy a1 ha1 p‖ ≤ 9*q ∧
    ‖commonSupportWeakEnergy a ha p-
      nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportWeakEnergy a1 ha1 p‖ ≤ 9*q ∧
    ‖commonSupportZeroWeakEnergy a ha p-
      nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportZeroWeakEnergy a1 ha1 p‖ ≤ 9*q := by
  have hDiff (x : X) (hx : x ∈ (ballOpens:Set X)) (i j : I) :
      |(a (p,x)-(1:ℝ) • (1:Mat)-r • a1 (p,x)) i j| ≤ q := by
    have hEq : a (p,x)-(1:ℝ) • (1:Mat)-r • a1 (p,x) = aD (p,x)-(1:Mat) := by
      rw [hField,one_smul]
      module
    rw [hEq]
    exact hJets i j x hx
  have hF := norm_unitBall_full_energy_affine_remainder_le (a:=fun z => a (p,z))
    (a0:=fun _ : X => (1:ℝ) • (1:Mat)) (a1:=fun z => a1 (p,z)) (commonSupportEnergyMemLp a ha p)
    (flatCoefficientBound 1) (commonSupportEnergyMemLp a1 ha1 p) r q hq hDiff
  have hW := norm_nativeWeakEnergy_affine_remainder_le (a:=fun z => a (p,z))
    (a0:=fun _ : X => (1:ℝ) • (1:Mat)) (a1:=fun z => a1 (p,z)) (commonSupportEnergyMemLp a ha p)
    (flatCoefficientBound 1) (commonSupportEnergyMemLp a1 ha1 p) r q hq hDiff
  have hZ := norm_nativeZeroCoefficientEnergy_affine_remainder_le (a:=fun z => a (p,z))
    (a0:=fun _ : X => (1:ℝ) • (1:Mat)) (a1:=fun z => a1 (p,z))
    (commonSupportEnergyMemLp a ha p) (flatCoefficientBound 1) (commonSupportEnergyMemLp a1 ha1 p) r q hq hDiff
  exact ⟨hF,hW,hZ⟩

attribute [local irreducible] commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

/-- Restriction to vectors of no greater norm preserves the norm of every
    parameter derivative of a smooth bilinear family. -/
lemma norm_iteratedFDeriv_bilinear_restriction_le
    {Q E F E0 F0 : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [NormedAddCommGroup F0] [NormedSpace ℝ F0]
    (A : Q → E →L[ℝ] F →L[ℝ] ℝ) (B : Q → E0 →L[ℝ] F0 →L[ℝ] ℝ)
    (J1 : E0 → E) (J2 : F0 → F) (p : Q) (hA : ContDiffAt ℝ ∞ A p) (hB : ContDiffAt ℝ ∞ B p)
    (hJ1 : ∀ u,‖J1 u‖ ≤ ‖u‖) (hJ2 : ∀ v,‖J2 v‖ ≤ ‖v‖)
    (hEq : ∀ t u v,B t u v = A t (J1 u) (J2 v)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n B p‖ ≤ ‖iteratedFDeriv ℝ n A p‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro b
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hAt := congrArg (fun f : Q → ℝ => iteratedFDeriv ℝ n f p b)
    (funext (fun t => hEq t u v))
  have hLeft := iteratedFDeriv_bilinear_apply_const B p n b u v hB
  have hRight := iteratedFDeriv_bilinear_apply_const A p n b (J1 u) (J2 v) hA
  have hPoint := hLeft.symm.trans (hAt.trans hRight)
  refine (congrArg norm hPoint).le.trans ?_
  exact (ContinuousLinearMap.le_opNorm₂ (iteratedFDeriv ℝ n A p b) (J1 u) (J2 v)).trans
    (mul_le_mul
      (mul_le_mul ((iteratedFDeriv ℝ n A p).le_opNorm b) (hJ1 u) (norm_nonneg _) (by positivity))
      (hJ2 v) (norm_nonneg _) (by positivity))

/-- All full, weak and zero-boundary native energy Taylor jets retain the
    local coefficient remainder budget, including derivative order zero. -/
theorem norm_iteratedFDeriv_commonSupport_weak_affine_remainder_le
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => commonSupportFullWeakEnergy a ha t-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-r • commonSupportFullWeakEnergy a1 ha1 t) p‖ ≤
        (9+weakFullDerivativeBudget)*q ∧
    ‖iteratedFDeriv ℝ n (fun t => commonSupportWeakEnergy a ha t-
      nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportWeakEnergy a1 ha1 t) p‖ ≤ (9+weakFullDerivativeBudget)*q ∧
    ‖iteratedFDeriv ℝ n (fun t => commonSupportZeroWeakEnergy a ha t-
      nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportZeroWeakEnergy a1 ha1 t) p‖ ≤ (9+weakFullDerivativeBudget)*q := by
  have hWB := weakFullDerivativeBudget_nonneg
  have hPointLE : 9*q ≤ (9+weakFullDerivativeBudget)*q :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hWB) hq
  have hPositiveLE : weakFullDerivativeBudget*q ≤ (9+weakFullDerivativeBudget)*q :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : 0 ≤ (9:ℝ))) hq
  have hFull :
      ‖iteratedFDeriv ℝ n (fun t => commonSupportFullWeakEnergy a ha t-
        TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-r • commonSupportFullWeakEnergy a1 ha1 t) p‖ ≤
          (9+weakFullDerivativeBudget)*q := by
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero] at hJets ⊢
      have hPoint := commonSupport_weak_affine_remainder_point_bound a a1 aD ha ha1 r hField p q hq
        (fun i j x hx => by simpa only [Real.norm_eq_abs] using hJets i j x hx)
      exact hPoint.1.trans hPointLE
    · have hn1 : 1 ≤ n := by omega
      have hMixed (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) :
          ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => aD (t,z) i j) x) p‖ ≤ q := by
        have he := iteratedFDeriv_parameter_spatial_sub_fixed_pos (fun v => aD v i j)
          (contDiff_pi.mp (contDiff_pi.mp haD i) j) (fun _ : X => (1:Mat) i j) contDiff_const p x n 0 hn1
        rw [← he]
        exact hJets i j x hx
      have hAffine (t : P) (z : X) (_ : z ∈ (ballOpens:Set X)) :
          a (t,z) = (0:ℝ) • (1:Mat)+r • a1 (t,z)+aD (t,z) := by
        rw [hField]
        module
      have hWeak := commonSupport_weakEnergy_affine_families a a1 aD ha ha1 haD 0 r hAffine
      rw [iteratedFDeriv_affine_family_positive_eq (P:=P) (V:=BallH1 →L[ℝ] StrongDual ℝ BallH1)
        _ _ _ _ _ r p n hn1 hWeak.1]
      exact (norm_iteratedFDeriv_commonSupportFullWeakEnergy_le aD haD SD hSD hzD p n q hq hMixed).trans hPositiveLE
  let Z : P → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero := fun t =>
    commonSupportZeroWeakEnergy a ha t-
      nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportZeroWeakEnergy a1 ha1 t
  let F : P → BallH1 →L[ℝ] StrongDual ℝ BallH1 := fun t =>
    commonSupportFullWeakEnergy a ha t-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-r • commonSupportFullWeakEnergy a1 ha1 t
  have hZ : ContDiffAt ℝ ∞ Z p :=
    (((contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt).sub contDiffAt_const).sub
      (((contDiff_commonSupportZeroWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt).const_smul r)
  have hF : ContDiffAt ℝ ∞ F p :=
    (((contDiff_commonSupportFullWeakEnergy a ha S hS hz).contDiffAt).sub contDiffAt_const).sub
      (((contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt).const_smul r)
  let W : P → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero := fun t =>
    commonSupportWeakEnergy a ha t-
      nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportWeakEnergy a1 ha1 t
  have hW : ContDiffAt ℝ ∞ W p :=
    (((contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt).sub contDiffAt_const).sub
      (((contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt).const_smul r)
  have hEqZ (t : P) (u v : BallH1Zero) : Z t u v = F t (u:BallH1) (v:BallH1) := by
    have ea := nativeZeroFullEnergy_eval (fun z => a (t,z)) (commonSupportEnergyMemLp a ha t) u v
    have e0 := nativeZeroFullEnergy_eval (fun _ : X => (1:ℝ) • (1:Mat)) (flatCoefficientBound 1) u v
    have e1 := nativeZeroFullEnergy_eval (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t) u v
    dsimp only [Z,F]
    delta commonSupportZeroWeakEnergy commonSupportFullWeakEnergy
    have hSub := congrArg₂ (fun x y : ℝ => x-y) ea e0
    have hResult := congrArg₂ (fun x y : ℝ => x-r*y) hSub e1
    change nativeZeroCoefficientEnergyL (fun z => a (t,z)) 0 0 (commonSupportEnergyMemLp a ha t) u v-
      nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1) u v-
      r*nativeZeroCoefficientEnergyL (fun z => a1 (t,z)) 0 0 (commonSupportEnergyMemLp a1 ha1 t) u v =
      TauCeti.PDE.energyFormH1L (commonSupportEnergyMemLp a ha t) (u:BallH1) (v:BallH1)-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound 1) (u:BallH1) (v:BallH1)-
      r*TauCeti.PDE.energyFormH1L (commonSupportEnergyMemLp a1 ha1 t) (u:BallH1) (v:BallH1)
    exact hResult
  have hWeakEval (b : X → Mat)
      (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
      (u : BallH1) (v : BallH1Zero) :
      nativeCoefficientWeakEnergyL b 0 0 hb u v = TauCeti.PDE.energyFormH1L hb u (v:BallH1) :=
    (nativeCoefficientWeakEnergyL_apply b (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) hb u v).trans
      (TauCeti.PDE.energyFormH1L_apply hb u (v:BallH1)).symm
  have hEqW (t : P) (u : BallH1) (v : BallH1Zero) : W t u v = F t u (v:BallH1) := by
    have ea := hWeakEval (fun z => a (t,z)) (commonSupportEnergyMemLp a ha t) u v
    have e0 := hWeakEval (fun _ : X => (1:ℝ) • (1:Mat)) (flatCoefficientBound 1) u v
    have e1 := hWeakEval (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t) u v
    dsimp only [W,F]
    delta commonSupportWeakEnergy commonSupportFullWeakEnergy
    have hSub := congrArg₂ (fun x y : ℝ => x-y) ea e0
    have hResult := congrArg₂ (fun x y : ℝ => x-r*y) hSub e1
    change nativeCoefficientWeakEnergyL (fun z => a (t,z)) 0 0 (commonSupportEnergyMemLp a ha t) u v-
      nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1) u v-
      r*nativeCoefficientWeakEnergyL (fun z => a1 (t,z)) 0 0 (commonSupportEnergyMemLp a1 ha1 t) u v =
      TauCeti.PDE.energyFormH1L (commonSupportEnergyMemLp a ha t) u (v:BallH1)-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound 1) u (v:BallH1)-
      r*TauCeti.PDE.energyFormH1L (commonSupportEnergyMemLp a1 ha1 t) u (v:BallH1)
    exact hResult
  have hC : 0 ≤ (9+weakFullDerivativeBudget)*q := by positivity
  refine ⟨hFull,?_,?_⟩
  · apply ContinuousMultilinearMap.opNorm_le_bound hC
    intro b
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
    intro u v
    have hAt := congrArg (fun f : P → ℝ => iteratedFDeriv ℝ n f p b) (funext (fun t => hEqW t u v))
    have hLeft := iteratedFDeriv_bilinear_apply_const W p n b u v hW
    have hRight := iteratedFDeriv_bilinear_apply_const F p n b u (v:BallH1) hF
    have hPoint := hLeft.symm.trans (hAt.trans hRight)
    refine (congrArg norm hPoint).le.trans ?_
    exact (ContinuousLinearMap.le_opNorm₂ (iteratedFDeriv ℝ n F p b) u (v:BallH1)).trans
      (by have h := ((iteratedFDeriv ℝ n F p).le_opNorm b).trans
            (mul_le_mul_of_nonneg_right hFull (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))
  · apply ContinuousMultilinearMap.opNorm_le_bound hC
    intro b
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
    intro u v
    have hAt := congrArg (fun f : P → ℝ => iteratedFDeriv ℝ n f p b) (funext (fun t => hEqZ t u v))
    have hLeft := iteratedFDeriv_bilinear_apply_const (Q:=P) (E:=BallH1Zero) (F:=BallH1Zero) Z p n b u v hZ
    have hRight := iteratedFDeriv_bilinear_apply_const F p n b (u:BallH1) (v:BallH1) hF
    have hPoint := hLeft.symm.trans (hAt.trans hRight)
    refine (congrArg norm hPoint).le.trans ?_
    exact (ContinuousLinearMap.le_opNorm₂ (iteratedFDeriv ℝ n F p b) (u:BallH1) (v:BallH1)).trans
      (by have h := ((iteratedFDeriv ℝ n F p).le_opNorm b).trans
            (mul_le_mul_of_nonneg_right hFull (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))

end ShrinkingSpheres
