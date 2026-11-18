import Proof.SmoothInverseFiniteJets
import Proof.ScalarConjugationDefect
import Proof.InverseAffineRemainderFactorization
import Proof.FiniteJetLinearCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
namespace SmoothFiniteJetBound
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma neg {f : P → E} {p : P} {N : ℕ} {B : ℝ}
    (h : SmoothFiniteJetBound f p N B) : SmoothFiniteJetBound (fun q => -f q) p N B := by
  simpa only [abs_neg,abs_one,one_mul,neg_one_smul] using h.const_smul (-1)
lemma congr_germ {f g : P → E} {p : P} {N : ℕ} {B : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hfg : f =ᶠ[𝓝 p] g) : SmoothFiniteJetBound g p N B := by
  refine ⟨hf.nonneg,hf.smooth.congr_of_eventuallyEq hfg.symm,?_⟩
  intro n hn
  rw [← (hfg.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hf.bound n hn
end SmoothFiniteJetBound

lemma conjugation_taylor_cancellation_finite_jets
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (M C R : P → E →L[ℝ] E) (p : P) (N : ℕ) (r BI BM BC BR : ℝ)
    (hM : ContDiffAt ℝ ∞ M p) (hInv : (M p).IsInvertible) (hr : 0 ≤ r)
    (hI : SmoothFiniteJetBound (fun q => (M q).inverse) p N BI)
    (hSmall : SmoothFiniteJetBound (fun q => M q-ContinuousLinearMap.id ℝ E) p N (BM*r))
    (hC : SmoothFiniteJetBound C p N BC) (hR : SmoothFiniteJetBound R p N (BR*r^2)) :
    SmoothFiniteJetBound (fun q => -(M q).inverse.comp (r • C q+R q)+r • C q) p N
      ((2^N*(2^N*BI*BM)*BC+2^N*BI*BR)*r^2) := by
  have hProduct := ((hI.comp hSmall).comp hC).const_smul r
  have hRest := (hI.comp hR).neg
  have hSum := hProduct.add hRest
  rw [abs_of_nonneg hr] at hSum
  have hBudget : r*(2^N*(2^N*BI*(BM*r))*BC)+2^N*BI*(BR*r^2)=
      (2^N*(2^N*BI*BM)*BC+2^N*BI*BR)*r^2 := by ring
  rw [hBudget] at hSum
  apply hSum.congr_germ
  filter_upwards [eventually_isInvertible_of_continuousAt M p hM.continuousAt hInv] with q hq
  rw [← inverse_defect_identity (M q) hq]
  simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,smul_sub]
  abel
end ShrinkingSpheres
