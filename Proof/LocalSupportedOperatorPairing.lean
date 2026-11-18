import Proof.SupportedOperatorCalculus
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ContDiff Topology
open OAI.AnisotropicCalderon
namespace ShrinkingSpheres.OperatorForms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma integrable_local_weighted_operator_pair
    (P : G →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (v : R3 → G) (u : R3 → E)
    (C : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) (hv : ContDiff ℝ ∞ v)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K,u x=0)
    (hC : ∀ x ∈ K,ContDiffAt ℝ ∞ C x) :
    Integrable (fun x => mu x*P (v x) (C x (u x))) := by
  let f := fun x => P (v x) (C x (u x))
  have hCS := contDiff_supported_operator_apply u C K hK.isClosed hu h0 hC
  have hf : ContDiff ℝ ∞ f := (P.contDiff.comp hv).clm_apply hCS
  have hf0 (x) (hx : x ∉ K) : f x=0 := by
    simp only [f,h0 x hx,map_zero]
  have hS := contDiff_supported_smul mu f K hK.isClosed hf hf0 hm
  have hKf : HasCompactSupport (fun x => mu x • f x) :=
    HasCompactSupport.intro hK (fun x hx => by rw [hf0 x hx,smul_zero])
  simpa only [smul_eq_mul,f] using hS.continuous.integrable_of_hasCompactSupport hKf
end ShrinkingSpheres.OperatorForms
