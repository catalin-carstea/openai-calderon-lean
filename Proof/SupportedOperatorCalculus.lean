/- Generic supported-operator proofs adopted from the selected ZIP; source ranges recorded separately. -/
import Proof.Archive.PrincipalDirectional
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
open OAI.AnisotropicCalderon OAI.AnisotropicCalderon.PrincipalCommutator
namespace ShrinkingSpheres.OperatorForms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma contDiffAt_directional (f : R3 → E) (x X : R3) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (directionalFDeriv X f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma directional_smul_at (s : R3 → ℝ) (v : R3 → E) (x X : R3)
    (hs : ContDiffAt ℝ ∞ s x) (hv : ContDiffAt ℝ ∞ v x) :
    directionalFDeriv X (fun y => s y • v y) x =
      directionalFDeriv X s x • v x+s x • directionalFDeriv X v x := by
  unfold directionalFDeriv
  rw [fderiv_fun_smul (hs.differentiableAt (by simp)) (hv.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,smul_apply]
  exact add_comm _ _

lemma tsupport_subset_of_zero_off (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (h0 : ∀ x ∉ K, u x = 0) : tsupport u ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (h0 x hn)

lemma directional_eq_zero_off (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (h0 : ∀ x ∉ K, u x = 0) (X x : R3) (hx : x ∉ K) :
    directionalFDeriv X u x = 0 := by
  have ht : x ∉ tsupport u := fun h => hx (tsupport_subset_of_zero_off u K hK h0 h)
  simp only [directionalFDeriv,fderiv_of_notMem_tsupport ℝ ht,ContinuousLinearMap.zero_apply]

 
lemma contDiff_supported_operator_apply (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) :
    ContDiff ℝ ∞ (fun x => C x (u x)) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ K
  · exact (hC x hx).clm_apply hu.contDiffAt
  · have he : (fun y => C y (u y)) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simp only [h0 y hy,map_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma compact_supported_operator_apply (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsCompact K) (h0 : ∀ x ∉ K, u x = 0) :
    HasCompactSupport (fun x => C x (u x)) :=
  HasCompactSupport.intro hK (fun x hx => by simp only [h0 x hx,map_zero])

lemma directional_operator_apply_supported (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X x : R3) :
    directionalFDeriv X (fun y => C y (u y)) x =
      (directionalFDeriv X C x) (u x)+C x (directionalFDeriv X u x) := by
  by_cases hx : x ∈ K
  · unfold directionalFDeriv
    rw [fderiv_clm_apply ((hC x hx).differentiableAt (by simp))
      (hu.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  · rw [directional_eq_zero_off (fun y => C y (u y)) K hK
        (fun y hy => by simp only [h0 y hy,map_zero]) X x hx,
      h0 x hx,directional_eq_zero_off u K hK h0 X x hx,map_zero,map_zero,add_zero]

lemma compact_bilinear_integrable (P : E →L[ℝ] F →L[ℝ] ℝ)
    (u : R3 → E) (v : R3 → F) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport v) : Integrable (fun x => P (u x) (v x)) := by
  apply ((P.continuous.comp hu).clm_apply hv).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [hx,map_zero]

 
lemma directional_linear_input (I : E →L[ℝ] G) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (X x : R3) :
    directionalFDeriv X (fun y => I (u y)) x = I (directionalFDeriv X u x) := by
  have h := directionalFDeriv_clm_apply X (fun _ : R3 => I) u contDiff_const hu x
  simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h

 
lemma contDiff_supported_smul (mu : R3 → ℝ) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K,u x=0) (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) :
    ContDiff ℝ ∞ (fun x => mu x • u x) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ K
  · exact (hm x hx).smul hu.contDiffAt
  · have he : (fun y => mu y • u y)=ᶠ[𝓝 x] (fun _ => (0:E)) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simp only [h0 y hy,smul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma directional_smul_supported (mu : R3 → ℝ) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K,u x=0) (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) (X x : R3) :
    directionalFDeriv X (fun y => mu y • u y) x=
      directionalFDeriv X mu x • u x+mu x • directionalFDeriv X u x := by
  by_cases hx : x ∈ K
  · exact directional_smul_at mu u x X (hm x hx) hu.contDiffAt
  · rw [directional_eq_zero_off (fun y => mu y • u y) K hK
      (fun y hy => by rw [h0 y hy,smul_zero]) X x hx,h0 x hx,
      directional_eq_zero_off u K hK h0 X x hx,smul_zero,smul_zero,add_zero]

end ShrinkingSpheres.OperatorForms
