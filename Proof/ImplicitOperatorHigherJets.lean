import Proof.InverseAffineRemainderFactorization
import Proof.AffineInverseFamilyJetBounds
import Proof.OperatorFamilyJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A true local left identity gives all finite jets of the same unknown
    operator family. Only the genuine inverse at the selected point is used. -/
theorem norm_iteratedFDeriv_operator_family_of_left_identity_le
    (M : P → F →L[ℝ] F) (J R : P → E →L[ℝ] F) (x : P)
    (hM : ContDiffAt ℝ ∞ M x) (hR : ContDiffAt ℝ ∞ R x)
    (hIdentity : (fun p => (M p).comp (J p)) =ᶠ[𝓝 x] R)
    (hInv : (M x).IsInvertible) (N : ℕ) (r CI DM CR : ℝ)
    (hCI : 0 ≤ CI) (hDM : 0 ≤ DM) (hCR : 0 ≤ CR) (hNI : ‖(M x).inverse‖ ≤ CI)
    (hMJets : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j M x‖ ≤ DM)
    (hRJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j R x‖ ≤ CR*r^2)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n J x‖ ≤ (2^N*inverseFamilyJetBudget N CI DM*CR)*r^2 := by
  let Inv := fun p => (M p).inverse
  have hInvMap : ContDiffAt ℝ ∞ (fun L : F →L[ℝ] F => L.inverse) (M x) := hInv.contDiffAt_map_inverse
  have hInvSmooth : ContDiffAt ℝ ∞ Inv x := hInvMap.comp x hM
  have hGerm : J =ᶠ[𝓝 x] (fun p => (Inv p).comp (R p)) := by
    filter_upwards [eventually_isInvertible_of_continuousAt M x hM.continuousAt hInv,hIdentity] with p hp hId
    dsimp only [Inv]
    rw [← hId,← ContinuousLinearMap.comp_assoc,hp.inverse_comp_self,ContinuousLinearMap.id_comp]
  have hInvJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j Inv x‖ ≤ inverseFamilyJetBudget N CI DM :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible M x hInv hM N CI DM hCI hDM hNI hMJets j hj
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact (norm_iteratedFDeriv_operator_comp_common_bound Inv R x hInvSmooth hR N
    (inverseFamilyJetBudget N CI DM) (CR*r^2) (inverseFamilyJetBudget_nonneg N CI DM hCI hDM)
    (by positivity) hInvJets hRJets n hn).trans_eq (by ring)

end ShrinkingSpheres
