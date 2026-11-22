module

public import Proof.CalderonN.ActualConstantTraceBound
public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.ShrinkingRadiusParameter

import Proof.CalderonN.MovingTraceBackgroundBounds
import Proof.CalderonN.ProfileBounds
import Mathlib.Tactic

/-! Adapted from `ConformalConstantTraceBound` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The constant-mode bound for the actual conformal shrinking spheres.
The bound is chosen before the dilation and smoothing parameters. -/
theorem exists_uniform_conformal_movingTrace_one_bound
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {K Y Y' Ω : Set (X dim)} (hK : IsCompact K) (hY : IsOpen Y) (hY' : IsOpen Y')
    (hYK : Y ⊆ K) (hKY' : K ⊆ Y')
    {p : ℕ} (hp : 1 ≤ p) {ρ R ε : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Y' Ω
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y, shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let g := dilatedMetric g₁ lam
      let k := dilatedMetric g₂ lam
      let e (y : (X dim)) := smoothMetricFrame (γ y)
      ∀ δ ∈ Ioc (0 : ℝ) 1,
      let r := shrinkingRadius R p (conformalDepth normal 4) δ
      let A := actualMovingTraceAdjoint γ g (E lam) e r
      Small Y γ k r ε → Dirichlet Y γ g (E lam) r → IsMovingTraceAdjoint Y γ g e (E lam) r A →
      ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        ‖movingTrace γ k r A (1 : (Field dim)) (y,frameVector e y w)‖ ≤ C := by
  let S := Icc (-1 : ℝ) 1
  let γ := conformalReference (depthScale normal 4) g₁
  let g := dilatedMetric g₁
  let k := dilatedMetric g₂
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  let depth := conformalDepth normal 4
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have hg (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₁.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hk (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => k q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₂.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hgp (lam : ℝ) (y : (X dim)) : (g lam y).PosDef := hg₁.2 _ (mem_univ _)
  have hkp (lam : ℝ) (y : (X dim)) : (k lam y).PosDef := hg₂.2 _ (mem_univ _)
  have hγp (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef := (hgp lam y).smul (depthScale_pos (normal := normal) 4 y)
  have he (i : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame
      (fun i j => (hγ i j).contDiffOn) (fun q _ => hγp q.1 q.2) i)
  have hFrame (lam : ℝ) (_ : lam ∈ S) (y : (X dim)) (_ : y ∈ K) (i j : (I dim)) :
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγp lam y) i j
  have hConf (lam : ℝ) (_ : lam ∈ S) (y : (X dim)) (_ : y ∈ K) :
      ∃ c : ℝ, 0 < c ∧ γ lam y = c • g lam y := ⟨depthScale normal 4 y,depthScale_pos (normal := normal) 4 y,rfl⟩
  obtain ⟨m,_,hm,_,hCov⟩ := exists_uniform_conformalDepth_covector_bounds (normal := normal) isOpen_univ (mem_univ _)
    hK hg₁ (by norm_num : 0 < (4 : ℝ))
  have hd : ContDiff ℝ ∞ depth := contDiff_conformalDepth (normal := normal) 4
  obtain ⟨D,hD,hJet⟩ := exists_shrinkingRadius_coordinate_derivative_bounds hd hK hm (half_pos hρ).le hε
  obtain ⟨P,Γ,T,hP,hΓ,hT,hCoeff⟩ :=
    exists_uniform_movingTrace_coefficients (S := S) isCompact_Icc hK hγ hγp hk hkp
  obtain ⟨L,hL,hGeom⟩ := exists_uniform_movingTrace_frame_geometry (S := S) isCompact_Icc hK hγ hγp he
  obtain ⟨C,hC,h⟩ := exists_uniform_actual_movingTrace_one_bound hγ hγp hg hgp hE he
    isCompact_Icc hK hY hY' hYK hKY' hρ hε hD hL hP hΓ hT hNormal hFrame hConf hCoeff hGeom
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hCov,hS] with lam hCov hlam
  dsimp only
  intro _ δ hδ hSmall hDir hA
  let r := shrinkingRadius R p depth δ
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius hd R p δ
  have hrad (y : (X dim)) (hy : y ∈ Y) : r y ∈ Ioc 0 (ρ/2) :=
    ⟨shrinkingRadius_pos hR hδ.1 p depth y,hRadius δ hδ y hy⟩
  have hJ (y : (X dim)) (hy : y ∈ Y) :=
    hJet (hYK hy) (γ lam) (hCov y (hYK hy)).2.1 hR hδ hp (hrad y hy).2 (hSmall y hy).2
  exact h lam hlam r hr hrad (fun y hy => (hJ y hy).1) (fun y hy => (hJ y hy).2) hSmall hDir hA

end CalderonN
