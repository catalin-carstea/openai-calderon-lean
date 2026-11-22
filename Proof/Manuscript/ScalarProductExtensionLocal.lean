module

public import Proof.Manuscript.ScalarProductExtensionGlobal

import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

private theorem connection_of_eventuallyEq {g G : MetricField n} {x : X n}
    (h : g =ᶠ[𝓝 x] G) (v w : X n) :
    connection g x v w = connection G x v w := by
  have hcoord (i j k : I n) :
      coordDeriv k (fun y => g y i j) x = coordDeriv k (fun y => G y i j) x := by
    have hij : (fun y => g y i j) =ᶠ[𝓝 x] (fun y => G y i j) :=
      h.mono fun y hy => congrFun (congrFun hy i) j
    exact congrArg (fun T : X n →L[ℝ] ℝ => T (axis k)) hij.fderiv_eq
  unfold connection christoffel
  simp only [h.eq_of_nhds,hcoord]

private theorem strictProduct_of_metricGerms
    {g₁ g₂ G₁ G₂ : MetricField n} {ρ : X n × X n → ℝ} {z : X n × X n}
    (h₁ : g₁ =ᶠ[𝓝 z.1] G₁) (h₂ : g₂ =ᶠ[𝓝 z.2] G₂)
    (h : ProductStrictHessianAt G₁ G₂ ρ z) : ProductStrictHessianAt g₁ g₂ ρ z := by
  simpa only [ProductStrictHessianAt,chartMetricGradient,covectorSq,metricPair,
    productMetricHessian,h₁.eq_of_nhds,h₂.eq_of_nhds,connection_of_eventuallyEq h₁,
    connection_of_eventuallyEq h₂] using h

omit [NeZero n] in
private theorem ProductSolvesOn.congr_operators {L₁ L₂ M₁ M₂ : ScalarElliptic n}
    {U : Set (X n × X n)} {F : X n × X n → ℝ} (hF : L₁.ProductSolvesOn L₂ U F)
    (h₁ : ∀ z ∈ U, ∀ u, M₁.apply u z.1 = L₁.apply u z.1)
    (h₂ : ∀ z ∈ U, ∀ u, M₂.apply u z.2 = L₂.apply u z.2) :
    M₁.ProductSolvesOn M₂ U F :=
  ⟨hF.1,fun z hz => (h₁ z hz _).trans (hF.2.1 z hz),fun z hz => (h₂ z hz _).trans (hF.2.2 z hz)⟩

set_option maxHeartbeats 3200000 in
/-- Local chart form of the fixed-reference product extension. The
same two plateaus globalize all operators and retain their germs near
the relevant closed coordinate rooms. -/
theorem exists_reference_scalar_productExtension
    {D₁ D₂ : Set (X n)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {L₁₀ L₂₀ : ScalarElliptic n} (hL₁₀ : L₁₀.SmoothOn D₁) (hL₂₀ : L₂₀.SmoothOn D₂)
    {U : Set (X n × X n)} (hU : IsOpen U) (hUD : U ⊆ D₁ ×ˢ D₂) (z₀ : X n × X n) (hz₀ : z₀ ∈ U)
    {ρ : X n × X n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρ₀ : ρ z₀ = 0)
    (hstrict : ProductStrictHessianAt L₁₀.metric L₂₀.metric ρ z₀) :
    ∃ (V : Set (X n × X n)) (K₁ K₂ K₃ K₄ : Set (X n)) (ε : ℝ),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ 0 < ε ∧
      IsCompact K₁ ∧ IsCompact K₂ ∧ IsCompact K₃ ∧ IsCompact K₄ ∧
      let K := (K₁ ×ˢ K₂) ∪ (K₃ ×ˢ K₄)
      let admissible := fun (L₁ L₂ : ℝ → ScalarElliptic n) (ρt : ℝ → (X n × X n) → ℝ) =>
        SmoothFamilyOn L₁ D₁ ∧ SmoothFamilyOn L₂ D₂ ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
        L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ ε ∧ ρt 0 = (fun z => ρ z - c)
      let side := fun (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) => {z ∈ U | 0 < ρt t z}
      (∀ L₁ L₂ ρt, admissible L₁ L₂ ρt →
        ∀ᶠ t in 𝓝 (0 : ℝ), K ⊆ {z ∈ U | ε < ρt t z}) ∧
      (∀ L₁ L₂ ρt, admissible L₁ L₂ ρt → ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F,
        (L₁ t).ProductSolvesOn (L₂ t) (side ρt t) F →
        ∃ G, (L₁ t).ProductSolvesOn (L₂ t) V G ∧ EqOn G F (V ∩ side ρt t)) ∧
      ∀ H ⊆ V, IsCompact H → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ L₁ L₂ ρt, admissible L₁ L₂ ρt →
        ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, (L₁ t).ProductSolvesOn (L₂ t) (side ρt t) F →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ K, |F z| ≤ M) →
        ∃ G, (L₁ t).ProductSolvesOn (L₂ t) V G ∧ EqOn G F (V ∩ side ρt t) ∧
          ∀ k ≤ m, ∀ z ∈ H, ‖iteratedFDeriv ℝ k G z‖ ≤ C*M := by
  obtain ⟨r₀,hr₀,hU₀⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  let r := r₀/2
  have hr : 0 < r := half_pos hr₀
  let H₁ := closedBall z₀.1 r
  let H₂ := closedBall z₀.2 r
  have hH₁ : IsCompact H₁ := isCompact_closedBall _ _
  have hH₂ : IsCompact H₂ := isCompact_closedBall _ _
  have hHU : H₁ ×ˢ H₂ ⊆ U := by
    rw [closedBall_prod_same]
    exact (closedBall_subset_ball (half_lt_self hr₀)).trans hU₀
  have hH₁D : H₁ ⊆ D₁ := fun x hx =>
    (hUD (hHU (show (x,z₀.2) ∈ H₁ ×ˢ H₂ from ⟨hx,mem_closedBall_self hr.le⟩))).1
  have hH₂D : H₂ ⊆ D₂ := fun y hy =>
    (hUD (hHU (show (z₀.1,y) ∈ H₁ ×ˢ H₂ from ⟨mem_closedBall_self hr.le,hy⟩))).2
  obtain ⟨χ₁,hχ₁,hχ₁D,hχ₁01,hχ₁one⟩ := exists_scalar_operator_cutoff hD₁ hH₁ hH₁D
  obtain ⟨χ₂,hχ₂,hχ₂D,hχ₂01,hχ₂one⟩ := exists_scalar_operator_cutoff hD₂ hH₂ hH₂D
  let e₁ (L : ScalarElliptic n) := cutoffOperator χ₁ L
  let e₂ (L : ScalarElliptic n) := cutoffOperator χ₂ L
  have hg₁ (L : ℝ → ScalarElliptic n) (hL : SmoothFamilyOn L D₁) :
      SmoothFamilyOn (e₁ ∘ L) univ := smoothFamilyOn_cutoffOperator hD₁ hχ₁ hχ₁D hχ₁01 hL
  have hg₂ (L : ℝ → ScalarElliptic n) (hL : SmoothFamilyOn L D₂) :
      SmoothFamilyOn (e₂ ∘ L) univ := smoothFamilyOn_cutoffOperator hD₂ hχ₂ hχ₂D hχ₂01 hL
  have hg₁₀ : (e₁ L₁₀).SmoothOn univ := (hg₁ (fun _ => L₁₀) (smoothFamilyOn_const hL₁₀)).1 0
  have hg₂₀ : (e₂ L₂₀).SmoothOn univ := (hg₂ (fun _ => L₂₀) (smoothFamilyOn_const hL₂₀)).1 0
  have hs : ProductStrictHessianAt (e₁ L₁₀).metric (e₂ L₂₀).metric ρ z₀ :=
    strictProduct_of_metricGerms (cutoffOperator_metric_germ (hχ₁one z₀.1 (mem_closedBall_self hr.le)))
      (cutoffOperator_metric_germ (hχ₂one z₀.2 (mem_closedBall_self hr.le))) hstrict
  let U' := ball z₀.1 r ×ˢ ball z₀.2 r
  have hU' : IsOpen U' := isOpen_ball.prod isOpen_ball
  have hU'H : U' ⊆ H₁ ×ˢ H₂ := Set.prod_mono ball_subset_closedBall ball_subset_closedBall
  have hU'U : U' ⊆ U := hU'H.trans hHU
  have hz' : z₀ ∈ U' := ⟨mem_ball_self hr,mem_ball_self hr⟩
  obtain ⟨V,K₁,K₂,K₃,K₄,ε,hV,hzV,hVU',hε,hK₁,hK₂,hK₃,hK₄,hArm,hQual,hQuant⟩ :=
    exists_global_reference_scalar_productExtension hg₁₀ hg₂₀ hU' z₀ hz' (hρ.mono hU'U) hρ₀ hs
  let K := (K₁ ×ˢ K₂) ∪ (K₃ ×ˢ K₄)
  let side (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) := {z ∈ U | 0 < ρt t z}
  let side' (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) := {z ∈ U' | 0 < ρt t z}
  have hSide (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) : side' ρt t ⊆ side ρt t :=
    fun z hz => ⟨hU'U hz.1,hz.2⟩
  let adm (L₁ L₂ : ℝ → ScalarElliptic n) (ρt : ℝ → (X n × X n) → ℝ) :=
    SmoothFamilyOn L₁ D₁ ∧ SmoothFamilyOn L₂ D₂ ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
    L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ ε ∧ ρt 0 = (fun z => ρ z-c)
  have hAdm' (L₁ L₂ ρt) (hL : adm L₁ L₂ ρt) :
      SmoothFamilyOn (e₁ ∘ L₁) univ ∧ SmoothFamilyOn (e₂ ∘ L₂) univ ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U') ∧
      (e₁ ∘ L₁) 0 = e₁ L₁₀ ∧ (e₂ ∘ L₂) 0 = e₂ L₂₀ ∧
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ ε ∧ ρt 0 = (fun z => ρ z-c) :=
    ⟨hg₁ L₁ hL.1,hg₂ L₂ hL.2.1,hL.2.2.1.mono (Set.prod_mono Subset.rfl hU'U),
      congrArg e₁ hL.2.2.2.1,congrArg e₂ hL.2.2.2.2.1,hL.2.2.2.2.2⟩
  have hInput (L₁ L₂ : ScalarElliptic n) (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) (F : X n × X n → ℝ)
      (hf : L₁.ProductSolvesOn L₂ (side ρt t) F) :
      (e₁ L₁).ProductSolvesOn (e₂ L₂) (side' ρt t) F :=
    (hf.mono (hSide ρt t)).congr_operators
      (fun z hz u => cutoffOperator_apply_of_one ((hχ₁one z.1 (hU'H hz.1).1).eq_of_nhds) u)
      (fun z hz u => cutoffOperator_apply_of_one ((hχ₂one z.2 (hU'H hz.1).2).eq_of_nhds) u)
  have hOutput (L₁ L₂ : ScalarElliptic n) (G : X n × X n → ℝ)
      (hG : (e₁ L₁).ProductSolvesOn (e₂ L₂) V G) : L₁.ProductSolvesOn L₂ V G :=
    hG.congr_operators
      (fun z hz u => (cutoffOperator_apply_of_one ((hχ₁one z.1 (hU'H (hVU' hz)).1).eq_of_nhds) u).symm)
      (fun z hz u => (cutoffOperator_apply_of_one ((hχ₂one z.2 (hU'H (hVU' hz)).2).eq_of_nhds) u).symm)
  have hAgree (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) :
      V ∩ side ρt t ⊆ V ∩ side' ρt t :=
    fun z hz => ⟨hz.1,hVU' hz.1,hz.2.2⟩
  refine ⟨V,K₁,K₂,K₃,K₄,ε,hV,hzV,hVU'.trans hU'U,hε,hK₁,hK₂,hK₃,hK₄,?_,?_,?_⟩
  · intro L₁ L₂ ρt hL
    filter_upwards [hArm (e₁ ∘ L₁) (e₂ ∘ L₂) ρt (hAdm' L₁ L₂ ρt hL)] with t ht z hz
    exact ⟨hU'U (ht hz).1,(ht hz).2⟩
  · intro L₁ L₂ ρt hL
    filter_upwards [hQual (e₁ ∘ L₁) (e₂ ∘ L₂) ρt (hAdm' L₁ L₂ ρt hL)] with t ht F hF
    obtain ⟨G,hG,hEq⟩ := ht F (hInput (L₁ t) (L₂ t) ρt t F hF)
    exact ⟨G,hOutput (L₁ t) (L₂ t) G hG,hEq.mono (hAgree ρt t)⟩
  · intro H hHV hH m
    obtain ⟨C,hC,ht⟩ := hQuant H hHV hH m
    refine ⟨C,hC,?_⟩
    intro L₁ L₂ ρt hL
    filter_upwards [ht (e₁ ∘ L₁) (e₂ ∘ L₂) ρt (hAdm' L₁ L₂ ρt hL)] with t ht F hf M hM hB
    obtain ⟨G,hG,hEq,hbound⟩ := ht F (hInput (L₁ t) (L₂ t) ρt t F hf) M hM hB
    exact ⟨G,hOutput (L₁ t) (L₂ t) G hG,hEq.mono (hAgree ρt t),hbound⟩

end CalderonPaper.ScalarElliptic
