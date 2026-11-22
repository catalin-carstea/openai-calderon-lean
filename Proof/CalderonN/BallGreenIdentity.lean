module

public import Proof.CalderonN.GreenCutoffPairing
public import Proof.CalderonN.WronskianFlux
public import Proof.CalderonN.SmoothBallDivergence

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

/-! The supported replacement at the boundary follows the argument of
`Calderon/MetricPointSourceBoundaryGreen.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc, with an arbitrary harmonic
Green slice on the collar. -/

@[expose] public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem laplace_germ {g : (MetricField dim)} {u v : (X dim) → ℝ} {x : (X dim)} (h : u =ᶠ[𝓝 x] v) :
    laplace g u x = laplace g v x := by
  obtain ⟨V,hV,hVo,hx⟩ := _root_.mem_nhds_iff.mp
    (show {z | u z = v z} ∈ 𝓝 x from h)
  exact laplace_congrOn hVo (fun _ _ => rfl) (fun _ hz => hV hz) hx

theorem wronskianFlux_congr_germ {g : (MetricField dim)} {u k k' : (X dim) → ℝ} {x : (X dim)}
    (h : k =ᶠ[𝓝 x] k') : wronskianFlux g u k x = wronskianFlux g u k' x := by
  rw [wronskianFlux,wronskianFlux,h.eq_of_nhds]
  simp only [divergenceFlux,coordDeriv,h.fderiv_eq]

theorem integral_greenCutoffSource_comm {U : Set (X dim)} (hU : IsOpen U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {f φ : (X dim) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    (∫ x, f x * greenCutoffSource g φ x) = ∫ x, φ x * greenCutoffSource g f x := by
  have h := congrArg Neg.neg (integral_laplace_symmetric_of_compact_test hU hg hf hφ hφc hs)
  rw [← integral_neg,← integral_neg] at h
  calc
    _ = ∫ x, -(f x * laplace g φ x * chartVolume g x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold greenCutoffSource
      ring
    _ = ∫ x, -(φ x * (chartVolume g x * laplace g f x)) := h
    _ = _ := by simp only [greenCutoffSource,mul_neg]

theorem exists_global_extension_on_closedUnitBall
    {U : Set (X dim)} (hU : IsOpen U) (hBU : closedBall (0 : (X dim)) 1 ⊆ U)
    {W : (X dim) → (X dim)} (hW : ContDiffOn ℝ ∞ W U) :
    ∃ W₀ : (X dim) → (X dim), ContDiff ℝ ∞ W₀ ∧
      ∀ x ∈ closedBall (0 : (X dim)) 1, W₀ =ᶠ[𝓝 x] W := by
  obtain ⟨χ,hχ,_,hχU,hχB⟩ := Elliptic.exists_plateau_cutoff hU
    (isCompact_closedBall _ _) hBU
  let W₀ := fun x => χ x • W x
  refine ⟨W₀,contDiff_iff_contDiffAt.mpr (fun x => ?_),?_⟩
  · by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hW.contDiffAt (hU.mem_nhds hx))
    · have hn : x ∈ (tsupport χ)ᶜ := fun h => hx (hχU h)
      have he : W₀ =ᶠ[𝓝 x] fun _ => (0 : (X dim)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with y hy
        simp only [W₀,image_eq_zero_of_notMem_tsupport hy,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    exact (hχB x hx).mono fun y hy => by simp [W₀,hy]

/-- A compact interior test and a Wronskian boundary flux have the same
value. The kernel slice is only required to be harmonic on the collar. -/
theorem greenCutoffSource_eq_unitSphereFlux
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : (X dim)) 1 ⊆ U)
    {a : ℝ} (ha : a < 1) (hCollar : closedBall (0 : (X dim)) 1 \ ball (0 : (X dim)) a ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric U g)
    {u k φ : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (huPDE : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hk : Harmonic S g k) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφB : tsupport φ ⊆ ball (0 : (X dim)) 1)
    (hφInner : EqOn φ u (ball (0 : (X dim)) a)) :
    (∫ x, k x * greenCutoffSource g φ x) = unitSphereFlux (wronskianFlux g u k) := by
  let K := closedBall (0 : (X dim)) 1 \ ball (0 : (X dim)) a
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  obtain ⟨χ,hχ,_,hχS,hχ1⟩ := Elliptic.exists_plateau_cutoff hS hK hCollar
  let M : (X dim) → ℝ := fun x => χ x * k x
  have hM : ContDiff ℝ ∞ M :=
    Elliptic.contDiff_mul_of_tsupport_subset hS hχ hχS hk.1
  have hMeq (x : (X dim)) (hx : x ∈ K) : M =ᶠ[𝓝 x] k :=
    (hχ1 x hx).mono fun y hy => by simp [M,hy]
  have hMlaw (x : (X dim)) (hx : x ∈ K) : greenCutoffSource g M x = 0 := by
    simp only [greenCutoffSource,laplace_germ (hMeq x hx),hk.2 x (hCollar hx),mul_zero,neg_zero]
  have hφU : tsupport φ ⊆ U := hφB.trans (ball_subset_closedBall.trans hBU)
  have hphiSource (x : (X dim)) (hx : x ∉ K) : greenCutoffSource g φ x = 0 := by
    by_cases hb : x ∈ ball (0 : (X dim)) 1
    · have hi : x ∈ ball (0 : (X dim)) a := by
        by_contra hn
        exact hx ⟨ball_subset_closedBall hb,hn⟩
      rw [greenCutoffSource,laplace_congrOn isOpen_ball (fun _ _ => rfl) hφInner hi,
        huPDE x hb,mul_zero,neg_zero]
    · exact image_eq_zero_of_notMem_tsupport (fun h => hb (hφB (tsupport_greenCutoffSource_subset g φ h)))
  let W := wronskianFlux g u M
  have hW : ContDiffOn ℝ ∞ W U := contDiffOn_wronskianFlux hU hg hu hM.contDiffOn
  obtain ⟨W₀,hW₀,hWnear⟩ := exists_global_extension_on_closedUnitBall hU hBU hW
  calc
    _ = ∫ x, M x * greenCutoffSource g φ x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ K
      · rw [(hMeq x hx).eq_of_nhds]
      · rw [hphiSource x hx,mul_zero,mul_zero]
    _ = ∫ x, φ x * greenCutoffSource g M x :=
      integral_greenCutoffSource_comm hU hg hM.contDiffOn hφ hφc hφU
    _ = ∫ x in ball (0 : (X dim)) 1, u x * greenCutoffSource g M x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun h => hx (hφB h))) _)]
      refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
      by_cases hi : x ∈ ball (0 : (X dim)) a
      · rw [hφInner hi]
      · rw [hMlaw x ⟨ball_subset_closedBall hx,hi⟩,mul_zero,mul_zero]
    _ = ∫ x in ball (0 : (X dim)) 1, coordinateFluxDivergence W₀ x := by
      refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
      rw [coordinateFluxDivergence_congr_germ (hWnear x (ball_subset_closedBall hx))]
      change u x * greenCutoffSource g M x =
        ∑ i, coordDeriv i (fun z => wronskianFlux g u M z i) x
      rw [divergence_wronskianFlux hU hg hu hM.contDiffOn (hBU (ball_subset_closedBall hx)),huPDE x hx]
      unfold greenCutoffSource
      ring
    _ = unitSphereFlux W₀ := integral_unitBall_coordinateFluxDivergence W₀ hW₀
    _ = _ := by
      unfold unitSphereFlux
      apply integral_congr_ae
      filter_upwards with w
      have hw : ‖(w : (X dim))‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
      have hwB : (w : (X dim)) ∈ closedBall (0 : (X dim)) 1 := mem_closedBall_zero_iff.mpr hw.le
      have hwK : (w : (X dim)) ∈ K := ⟨hwB,fun h => ha.not_ge (hw ▸ (mem_ball_zero_iff.mp h)).le⟩
      rw [(hWnear w hwB).eq_of_nhds]
      exact congrArg (fun Z : (X dim) => ⟪(w : (X dim)), Z⟫_ℝ) (wronskianFlux_congr_germ (u := u) (hMeq w hwK))

end CalderonN
