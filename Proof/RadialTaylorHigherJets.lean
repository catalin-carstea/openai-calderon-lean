import Proof.ImplicitOperatorHigherJets
import Proof.RadialTaylorLeftIdentity
import Proof.FiniteJetBudgetAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma norm_iteratedFDeriv_fintype_sum_at_le
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (f : ι → P → V) (x : P) (hf : ∀ i,ContDiffAt ℝ ∞ (f i) x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => ∑ i,f i p) x‖ ≤ ∑ i,‖iteratedFDeriv ℝ n (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (𝕜:=ℝ) (n:=n) (x:=x)
    (f:=f) (u:=Finset.univ) (fun i _ => (hf i).of_le (by simp))]
  exact norm_sum_le _ _

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialTaylorRhsJetBudget (N : ℕ) (D : E →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (CN CMQ CT CMD CB : ℝ) : ℝ :=
  CN+‖D‖*CMQ+CT*(∑ j : Fin 3,‖G j‖)+2^N*CMD*CB

/-- Every finite mixed jet of the exact radial left-hand forcing retains
    radius squared, including its tangential and first-normal cross terms. -/
theorem norm_iteratedFDeriv_radial_taylor_rhs_le
    (NQ B : P → E →L[ℝ] F) (MQ M : P → F →L[ℝ] F)
    (T : Fin 3 → P → F →L[ℝ] F) (D : E →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (x : P) (hNQ : ContDiffAt ℝ ∞ NQ x) (hB : ContDiffAt ℝ ∞ B x)
    (hMQ : ContDiffAt ℝ ∞ MQ x) (hM : ContDiffAt ℝ ∞ M x)
    (hT : ∀ j,ContDiffAt ℝ ∞ (T j) x) (N : ℕ) (c r CN CMQ CT CMD CB : ℝ)
    (hr : 0 ≤ r) (hCN : 0 ≤ CN) (hCMQ : 0 ≤ CMQ) (hCT : 0 ≤ CT) (hCMD : 0 ≤ CMD) (hCB : 0 ≤ CB)
    (hNQJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j NQ x‖ ≤ CN*r^2)
    (hMQJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j MQ x‖ ≤ CMQ*r^2)
    (hTJets : ∀ (k : Fin 3) (j : ℕ),j ≤ N → ‖iteratedFDeriv ℝ j (T k) x‖ ≤ CT*r^2)
    (hMDJets : ∀ j : ℕ,j ≤ N →
      ‖iteratedFDeriv ℝ j (fun p => M p-c • ContinuousLinearMap.id ℝ F) x‖ ≤ CMD*r)
    (hBJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j B x‖ ≤ CB)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => NQ p-(MQ p).comp D-∑ j : Fin 3,(T j p).comp (G j)-
      r • (M p-c • ContinuousLinearMap.id ℝ F).comp (B p)) x‖ ≤
        radialTaylorRhsJetBudget N D G CN CMQ CT CMD CB*r^2 := by
  let MD := fun p => M p-c • ContinuousLinearMap.id ℝ F
  let Q := fun p => (MQ p).comp D
  let S := fun p => ∑ j : Fin 3,(T j p).comp (G j)
  let C := fun p => (MD p).comp (B p)
  have hMD : ContDiffAt ℝ ∞ MD x := hM.sub contDiffAt_const
  have hQ : ContDiffAt ℝ ∞ Q x := hMQ.clm_comp contDiffAt_const
  have hS : ContDiffAt ℝ ∞ S x := ContDiffAt.sum (fun j _ => (hT j).clm_comp contDiffAt_const)
  have hC : ContDiffAt ℝ ∞ C x := hMD.clm_comp hB
  have hQN : ‖iteratedFDeriv ℝ n Q x‖ ≤ (‖D‖*CMQ)*r^2 :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le MQ D x hMQ n).trans
      ((mul_le_mul_of_nonneg_left (hMQJets n hn) (norm_nonneg _)).trans_eq (by ring))
  have hSN : ‖iteratedFDeriv ℝ n S x‖ ≤ (CT*∑ j : Fin 3,‖G j‖)*r^2 := by
    have hSum := norm_iteratedFDeriv_fintype_sum_at_le
      (fun j : Fin 3 => fun p => (T j p).comp (G j)) x (fun j => (hT j).clm_comp contDiffAt_const) n
    exact hSum.trans ((Finset.sum_le_sum (fun j _ =>
      (norm_iteratedFDeriv_operator_precomp_fixed_le (T j) (G j) x (hT j) n).trans
        (mul_le_mul_of_nonneg_left (hTJets j n hn) (norm_nonneg _)))).trans_eq
          (by rw [← Finset.sum_mul];ring))
  have hCN' : ‖iteratedFDeriv ℝ n C x‖ ≤ (2^N*CMD*CB)*r :=
    (norm_iteratedFDeriv_operator_comp_common_bound MD B x hMD hB N (CMD*r) CB
      (by positivity) hCB hMDJets hBJets n hn).trans_eq (by ring)
  have hRCN : ‖iteratedFDeriv ℝ n (fun p => r • C p) x‖ ≤ (2^N*CMD*CB)*r^2 := by
    rw [norm_iteratedFDeriv_const_smul_at C x hC r n,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hCN' hr).trans_eq (by ring)
  have h1 := norm_iteratedFDeriv_sub_at_le NQ Q x hNQ hQ n
  have h2 := norm_iteratedFDeriv_sub_at_le (fun p => NQ p-Q p) S x (hNQ.sub hQ) hS n
  have h3 := norm_iteratedFDeriv_sub_at_le (fun p => NQ p-Q p-S p) (fun p => r • C p)
    x ((hNQ.sub hQ).sub hS) (hC.const_smul r) n
  exact h3.trans ((add_le_add (h2.trans (add_le_add (h1.trans
    (add_le_add (hNQJets n hn) hQN)) hSN)) hRCN).trans_eq (by unfold radialTaylorRhsJetBudget;ring))

end ShrinkingSpheres
