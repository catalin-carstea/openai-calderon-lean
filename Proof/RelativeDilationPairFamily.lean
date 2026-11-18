import Proof.CommonSupportDilationNative
import Proof.GeneralLocalCommonSupportFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- One compact extension retains both actual dilation families on a common
    parameter neighborhood and the entire closed spatial ball. -/
theorem exists_relative_dilation_pair_family (f f1 : X → Mat)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0:X) 3))
    (hf1 : ContDiffOn ℝ ∞ f1 (Metric.ball (0:X) 3)) :
    ∃ A A1 : ℝ × X → Mat,ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ A1 ∧
      ∃ S : Set X,IsCompact S ∧ (∀ t z,z ∉ S → A (t,z) = 0) ∧
      (∀ t z,z ∉ S → A1 (t,z) = 0) ∧ ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)] relativeDilationFamily f) ∧
      ∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)] relativeDilationFamily f1 := by
  let scale : ℝ × X → X := fun p => (1+p.1) • p.2
  have hScale : ContDiff ℝ ∞ scale := (contDiff_const.add contDiff_fst).smul contDiff_snd
  let U := scale ⁻¹' Metric.ball (0:X) 3
  have hU : IsOpen U := Metric.isOpen_ball.preimage hScale.continuous
  let B0 : ℝ × X → Mat × Mat := fun p => (relativeDilationFamily f p,relativeDilationFamily f1 p)
  have hB0 : ContDiffOn ℝ ∞ B0 U := by
    intro p hp
    have hfAt := hf.contDiffAt (Metric.isOpen_ball.mem_nhds hp)
    have hf1At := hf1.contDiffAt (Metric.isOpen_ball.mem_nhds hp)
    exact ((hfAt.comp p hScale.contDiffAt).prodMk (hf1At.comp p hScale.contDiffAt)).contDiffWithinAt
  have hSub : {(0:ℝ)} ×ˢ Metric.closedBall (0:X) 2 ⊆ U := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    have ht0 : t = 0 := ht
    subst t
    have hz3 : z ∈ Metric.ball (0:X) 3 := by
      have hDist : dist z 0 ≤ 2 := hz
      change dist z 0 < 3
      linarith
    simpa only [U,mem_preimage,scale,add_zero,one_smul] using hz3
  obtain ⟨B,hB,S,hS,hSupport,V,hV,h0V,hVSub,hRep⟩ :=
    exists_local_commonSupport_family_on_open isOpen_univ B0 2 U hU hB0 (mem_univ (0:ℝ)) hSub
  let A : ℝ × X → Mat := fun p => (B p).1
  let A1 : ℝ × X → Mat := fun p => (B p).2
  have hA : ContDiff ℝ ∞ A := hB.fst
  have hA1 : ContDiff ℝ ∞ A1 := hB.snd
  have hz : ∀ t z,z ∉ S → A (t,z) = 0 := by
    intro t z hzS
    change (B (t,z)).1 = 0
    rw [hSupport t z hzS]
    rfl
  have hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0 := by
    intro t z hzS
    change (B (t,z)).2 = 0
    rw [hSupport t z hzS]
    rfl
  refine ⟨A,A1,hA,hA1,S,hS,hz,hz1,V,hV,h0V,?_,?_⟩
  · intro t ht z hzB
    filter_upwards [hRep t ht z hzB] with p hp
    exact congrArg Prod.fst hp
  · intro t ht z hzB
    filter_upwards [hRep t ht z hzB] with p hp
    exact congrArg Prod.snd hp

end ShrinkingSpheres
