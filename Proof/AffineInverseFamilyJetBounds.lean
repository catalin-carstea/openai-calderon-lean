import Proof.BanachInverseFamilyJetBounds
import Proof.OperatorFamilyJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def inverseFamilyJetBudget (N : ℕ) (I D : ℝ) : ℝ :=
  I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*D)^N)

lemma inverseFamilyJetBudget_nonneg (N : ℕ) (I D : ℝ) (hI : 0 ≤ I) (hD : 0 ≤ D) :
    0 ≤ inverseFamilyJetBudget N I D := by unfold inverseFamilyJetBudget;positivity

variable {P E F U Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def affineInverseCorrectionFamily (J : E →L[ℝ] U) (H : Z →L[ℝ] U)
    (A : P → E →L[ℝ] F) (B : P → U →L[ℝ] F) (p : P) : Z →L[ℝ] U :=
  H-J.comp (((A p).inverse.comp (B p)).comp H)

def affineInverseCorrectionJetBudget (N : ℕ) (I DA DB : ℝ)
    (J : E →L[ℝ] U) (H : Z →L[ℝ] U) : ℝ :=
  ‖H‖+‖J‖*‖H‖*(2^N*inverseFamilyJetBudget N I DA*DB)

lemma affineInverseCorrectionJetBudget_nonneg (N : ℕ) (I DA DB : ℝ)
    (hI : 0 ≤ I) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB) (J : E →L[ℝ] U) (H : Z →L[ℝ] U) :
    0 ≤ affineInverseCorrectionJetBudget N I DA DB J H := by
  unfold affineInverseCorrectionJetBudget
  have hh := inverseFamilyJetBudget_nonneg N I DA hI hDA
  positivity

theorem contDiffAt_affineInverseCorrectionFamily
    (J : E →L[ℝ] U) (H : Z →L[ℝ] U) (A : P → E →L[ℝ] F) (B : P → U →L[ℝ] F)
    (x : P) (hAx : (A x).IsInvertible) (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (affineInverseCorrectionFamily J H A B) x := by
  have hI : ContDiffAt ℝ ∞ (fun p => (A p).inverse) x := hAx.contDiffAt_map_inverse.comp x hA
  exact contDiffAt_const.sub (contDiffAt_const.clm_comp ((hI.clm_comp hB).clm_comp contDiffAt_const))

/-- Quantitative higher jets of the actual affine Dirichlet correction.
    The only inverse premise is the genuine inverse at the selected point. -/
theorem norm_iteratedFDeriv_affineInverseCorrectionFamily_le
    (J : E →L[ℝ] U) (H : Z →L[ℝ] U) (A : P → E →L[ℝ] F) (B : P → U →L[ℝ] F)
    (x : P) (hAx : (A x).IsInvertible) (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (N : ℕ) (I DA DB : ℝ) (hI : 0 ≤ I) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hInv : ‖(A x).inverse‖ ≤ I)
    (hAJets : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j A x‖ ≤ DA)
    (hBJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j B x‖ ≤ DB)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (affineInverseCorrectionFamily J H A B) x‖ ≤
      affineInverseCorrectionJetBudget N I DA DB J H := by
  let Inv := fun p => (A p).inverse
  let C := fun p => (Inv p).comp (B p)
  have hInvSmooth : ContDiffAt ℝ ∞ Inv x := hAx.contDiffAt_map_inverse.comp x hA
  have hC : ContDiffAt ℝ ∞ C x := hInvSmooth.clm_comp hB
  have hInvJet (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j Inv x‖ ≤ inverseFamilyJetBudget N I DA :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible A x hAx hA N I DA hI hDA hInv hAJets j hj
  have hCJ := norm_iteratedFDeriv_operator_comp_common_bound Inv B x hInvSmooth hB N
    (inverseFamilyJetBudget N I DA) DB (inverseFamilyJetBudget_nonneg N I DA hI hDA) hDB hInvJet hBJets n hn
  have hSand := norm_iteratedFDeriv_operator_sandwich_le J H C x hC n
  have hDiff := norm_iteratedFDeriv_const_sub_le (fun p => J.comp ((C p).comp H)) x
    (contDiffAt_const.clm_comp (hC.clm_comp contDiffAt_const)) H n
  exact hDiff.trans (add_le_add le_rfl (hSand.trans (mul_le_mul_of_nonneg_left hCJ (by positivity))))

end ShrinkingSpheres
