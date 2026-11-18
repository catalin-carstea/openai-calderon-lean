import Proof.OrderedDirectionalHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivative evaluated at a normalized parameter has controlled higher
    mixed jets. The outer small factor is retained through composition and
    evaluation, using only positive normalization jets. -/
theorem norm_iteratedFDeriv_normalizedDirectional_common_bound
    (F : P → E) (Q V : P → P) (p : P)
    (hF : ContDiffAt ℝ ∞ F (Q p)) (hQ : ContDiffAt ℝ ∞ Q p)
    (hV : ContDiffAt ℝ ∞ V p) (N : ℕ) (C D A : ℝ)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (hFJets : ∀ j : ℕ,j ≤ N+1 → ‖iteratedFDeriv ℝ j F (Q p)‖ ≤ C)
    (hQJets : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j Q p‖ ≤ D)
    (hVJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j V p‖ ≤ A)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ F (Q x) (V x)) p‖ ≤
      (2^N*A*(N.factorial:ℝ)*D^N)*C := by
  have hDF := hF.fderiv_right (m:=∞) (by simp)
  have hDFJets (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fderiv ℝ F) (Q p)‖ ≤ C := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hFJets (j+1) (by omega)
  have hGJets (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j ((fderiv ℝ F) ∘ Q) p‖ ≤ (N.factorial:ℝ)*C*D^N :=
    iteratedFDeriv_comp_common_bound Q (fderiv ℝ F) p hQ hDF N C D hC hD hDFJets hQJets j hj
  let ev : P →L[ℝ] (P →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E
  have hev : ‖ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro B
    exact (B.le_opNorm u).trans_eq (by ring)
  have hh := norm_iteratedFDeriv_bilinear_common_bound ev V ((fderiv ℝ F) ∘ Q) p
    hV (hDF.comp p hQ) N A ((N.factorial:ℝ)*C*D^N) hA (by positivity)
    hVJets hGJets n hn
  change ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ F (Q x) (V x)) p‖ ≤ _ at hh
  calc
    _ ≤ ‖ev‖*2^N*A*((N.factorial:ℝ)*C*D^N) := hh
    _ ≤ 1*2^N*A*((N.factorial:ℝ)*C*D^N) := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
