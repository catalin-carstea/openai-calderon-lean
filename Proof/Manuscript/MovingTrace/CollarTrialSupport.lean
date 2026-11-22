module

public import Proof.Manuscript.MovingTrace.LiftedTrialBoundaryReadout
public import Proof.Manuscript.MovingTrace.CutTrialResidual
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 3300000

open CalderonN CalderonPatch.BoundaryLayer Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

def collarDepthCutoff (δ t : ℝ) : ℝ :=
  Real.smoothTransition ((4*δ^2-t^2)/(3*δ^2))

theorem collarDepthCutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (collarDepthCutoff δ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

theorem collarDepthCutoff_one {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    collarDepthCutoff δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hq := (sq_le_sq₀ (abs_nonneg t) hδ.le).mpr ht
  rw [sq_abs] at hq
  exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)

theorem collarDepthCutoff_zero {δ t : ℝ} (hδ : 0 < δ) (ht : 2*δ ≤ |t|) :
    collarDepthCutoff δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hq := (sq_le_sq₀ (by positivity) (abs_nonneg t)).mpr ht
  rw [sq_abs] at hq
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

theorem collarDepthCutoff_derivatives_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo (-δ) δ) :
    deriv (collarDepthCutoff δ) t = 0 ∧ deriv (deriv (collarDepthCutoff δ)) t = 0 := by
  have he : collarDepthCutoff δ =ᶠ[𝓝 t] 1 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with q hq
    exact collarDepthCutoff_one hδ (abs_le.mpr ⟨hq.1.le,hq.2.le⟩)
  have hD : deriv (collarDepthCutoff δ) =ᶠ[𝓝 t] deriv (1 : ℝ → ℝ) := he.deriv
  exact ⟨by rw [he.deriv_eq]; simp,by rw [hD.deriv_eq]; simp⟩

theorem collarDepthCutoff_hasDerivAt_zero {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (collarDepthCutoff δ) 0 0 := by
  have hd := (collarDepthCutoff_contDiff δ).differentiable (by simp) (0:ℝ)
  have hD := hd.hasDerivAt
  rw [(collarDepthCutoff_derivatives_zero hδ (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith,hδ⟩)).1] at hD
  exact hD

theorem polarCollar_norm (v : ↥S) (x : X n) {t : ℝ} (ht : t ≤ 1) :
    ‖polarCollar (angularPoint v) (x,t)‖ = 1-t := by
  change ‖(1-t) • angularPoint v x‖ = _
  rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr ht),angularPoint_norm,mul_one]

theorem finiteWave_eq_zero_of_lon_or_depth
    {U K : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) (hK : IsClosed K) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K, a q = 0) {Kx : Set (X n)} (hKx : ∀ q ∈ K, q.2 ∈ Kx)
    {δ : ℝ} (hδ : 0 < δ) (phase : P × X n → ℝ) (M : ℕ) (h : ℝ) (p : P)
    (q : X n × ℝ) (hq : q ∉ Kx ×ˢ Icc (-2*δ) (2*δ)) :
    B.finiteWave a (collarDepthCutoff δ) phase M h ((p,q.1),q.2) = 0 := by
  unfold ParametricLayerCoefficients.finiteWave
  rw [Finset.sum_eq_zero, mul_zero]
  intro i hi
  by_cases hx : q.1 ∈ Kx
  · have hd : 2*δ ≤ |q.2| := by
      by_contra! h
      obtain ⟨hlo,hhi⟩ := abs_lt.mp h
      exact hq ⟨hx,by constructor <;> linarith⟩
    simp only [cutoffProfileFamily,collarDepthCutoff_zero hδ hd,zero_smul,mul_zero]
  · have hp : (p,q.1) ∉ K := fun h => hx (hKx _ h)
    simp [cutoffProfileFamily,polynomialProfileFamily,polynomialProfile,
      (B.layerPolynomial_properties hU hK a ha ha0 i).2.2 (p,q.1) hp]

theorem residual_cutTrialResidual_zero_off_signed_collar
    (v : ↥S) {Kx : Set (X n)} (hKx : IsCompact Kx)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : 2*δ < 1)
    {u : P × Z → ℂ} {a : P × Z → Mat (n+1)}
    (hSupp : ∀ p z, z ∉ (stereographicPolarCollar v) '' (Kx ×ˢ Icc (-2*δ) (2*δ)) → u (p,z) = 0)
    {h : ℝ} (hh : 0 < h) (hhδ : h ≤ δ/2) (p : P) {z : Z}
    (hz : z ∉ (stereographicPolarCollar v) '' (Kx ×ˢ Icc (-δ/2) (2*δ))) :
    cutTrialResidual a u h (p,z) = 0 := by
  let e := stereographicPolarCollar v
  let K := Kx ×ˢ Icc (-2*δ) (2*δ)
  have hK : IsCompact K := hKx.prod isCompact_Icc
  have hKS : K ⊆ e.source := fun q hq => hq.2.2.trans_lt hδ₁
  have hImage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKS)
  by_cases hq : z ∈ e '' K
  · obtain ⟨q,hq,rfl⟩ := hq
    have ht : q.2 < -δ/2 := lt_of_not_ge (fun h => hz ⟨q,⟨hq.1,h,hq.2.2⟩,rfl⟩)
    have he : ‖e q‖ = 1-q.2 := polarCollar_norm v q.1 (hKS hq).le
    have hScale : (1-‖e q‖)/h ≤ -1 := by
      rw [he,show 1 - (1-q.2) = q.2 by ring]
      apply (div_le_iff₀ hh).mpr
      linarith
    simp [cutTrialResidual,residualCutIn_zero hScale]
  · exact cutTrialResidual_zero_off_support hImage.isClosed hSupp h p hq

end CalderonPaper
