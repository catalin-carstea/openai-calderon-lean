import Proof.LinearFamilyJetEvaluation
import Proof.FiniteJetBoundCalculus
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def denseIsometryOperatorExtensionLinear (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e) :
    (E →L[ℝ] V) →ₗ[ℝ] (F →L[ℝ] V) where
  toFun L := L.extend e
  map_add' L M := by
    apply DFunLike.coe_injective
    apply hDense.equalizer ((L+M).extend e).continuous (L.extend e+M.extend e).continuous
    funext x
    change (L+M).extend e (e x) = L.extend e (e x)+M.extend e (e x)
    rw [(L+M).extend_eq hDense hIso.isUniformInducing x,L.extend_eq hDense hIso.isUniformInducing x,
      M.extend_eq hDense hIso.isUniformInducing x]
    rfl
  map_smul' c L := by
    apply DFunLike.coe_injective
    apply hDense.equalizer ((c • L).extend e).continuous (c • L.extend e).continuous
    funext x
    change (c • L).extend e (e x) = c • L.extend e (e x)
    rw [(c • L).extend_eq hDense hIso.isUniformInducing x,L.extend_eq hDense hIso.isUniformInducing x]
    rfl

theorem norm_denseIsometryOperatorExtension_le (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e)
    (L : E →L[ℝ] V) : ‖L.extend e‖ ≤ ‖L‖ := by
  have hh := L.opNorm_extend_le (N:=1) hDense (fun x => by
    simpa only [hIso.norm_map_of_map_zero e.map_zero,NNReal.coe_one,one_mul] using (le_refl ‖x‖))
  simpa only [NNReal.coe_one,one_mul] using hh

def denseIsometryOperatorExtensionL (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e) :
    (E →L[ℝ] V) →L[ℝ] (F →L[ℝ] V) :=
  (denseIsometryOperatorExtensionLinear e hDense hIso).mkContinuous 1
    (fun L => (norm_denseIsometryOperatorExtension_le e hDense hIso L).trans_eq (one_mul _).symm)

theorem norm_denseIsometryOperatorExtensionL_le_one (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e) :
    ‖denseIsometryOperatorExtensionL (V:=V) e hDense hIso‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem denseIsometryOperatorExtensionL_apply (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e)
    (L : E →L[ℝ] V) (x : E) : denseIsometryOperatorExtensionL e hDense hIso L (e x) = L x :=
  L.extend_eq hDense hIso.isUniformInducing x

/-- Completion of the linear input preserves gained operator jets before
    applying a moving completed input. No smoothness into a nonclosed smooth
    coefficient subspace is assumed. -/
theorem norm_iteratedFDeriv_moving_extended_linear_family_le
    (e : E →L[ℝ] F) (hDense : DenseRange e) (hIso : Isometry e)
    (L : P → E →L[ℝ] V) (q : P → F) (x : P)
    (hL : ContDiffAt ℝ ∞ L x) (hq : ContDiffAt ℝ ∞ q x)
    (N : ℕ) (r C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hFixed : ∀ n : ℕ,n ≤ N → ∀ u : E,‖iteratedFDeriv ℝ n (fun p => L p u) x‖ ≤ C*‖u‖*r^2)
    (hqJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n q x‖ ≤ B)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => denseIsometryOperatorExtensionL e hDense hIso (L p) (q p)) x‖ ≤
      (2^N*C*B)*r^2 := by
  let Ext := denseIsometryOperatorExtensionL (V:=V) e hDense hIso
  let LX := Ext ∘ L
  have hLX : ContDiffAt ℝ ∞ LX x := Ext.contDiff.contDiffAt.comp x hL
  have hExt : ‖Ext‖ ≤ 1 := norm_denseIsometryOperatorExtensionL_le_one e hDense hIso
  have hLJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j L x‖ ≤ C*r^2 :=
    norm_iteratedFDeriv_linear_family_of_apply_le L x hL j (C*r^2) (by positivity)
      (fun u => (hFixed j hj u).trans_eq (by ring))
  have hLXJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j LX x‖ ≤ C*r^2 :=
    (norm_iteratedFDeriv_clm_comp_le Ext L x hL j).trans
      ((mul_le_mul hExt (hLJets j hj) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  let ev : F →L[ℝ] (F →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V
  have hEv : ‖ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro A
    exact (A.le_opNorm u).trans_eq (by ring)
  have hh := norm_iteratedFDeriv_bilinear_common_bound ev q LX x hq hLX N B (C*r^2)
    hB (by positivity) hqJets hLXJets n hn
  exact hh.trans (by
    calc
      _ = ‖ev‖*((2^N*C*B)*r^2) := by ring
      _ ≤ 1*((2^N*C*B)*r^2) := mul_le_mul_of_nonneg_right hEv (by positivity)
      _ = _ := one_mul _)

end ShrinkingSpheres
