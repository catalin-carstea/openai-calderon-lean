module

public import Proof.CalderonPatch.NativeBoundaryLayerOperator
public import Proof.CalderonPatch.NativeBoundaryLayerTaylorError
public import Proof.CalderonPatch.BoundaryLayerPhysicalResidual

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

public section

noncomputable section
open Set Finset
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I MetricField laplace)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n + 1)

private theorem fderiv_layer_sum {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset β) (a : β → ℂ) (f : β → E → ℂ)
    (hf : ∀ j ∈ S, ContDiff ℝ ∞ (f j)) (x v : E) :
    fderiv ℝ (fun y => ∑ j ∈ S, a j * f j y) x v =
      ∑ j ∈ S, a j * fderiv ℝ (f j) x v := by
  rw [fderiv_fun_sum (fun j hj => (contDiff_const.mul (hf j hj)).differentiable (by simp) x),
    _root_.sum_apply]
  apply sum_congr rfl
  intro j hj
  rw [fderiv_const_mul (((hf j hj).differentiable (by simp)) x)]
  rfl

private theorem deriv_layer_sum {β : Type*} (S : Finset β) (a : β → ℂ) (f : β → ℝ → ℂ)
    (hf : ∀ j ∈ S, ContDiff ℝ ∞ (f j)) (x : ℝ) :
    deriv (fun y => ∑ j ∈ S, a j * f j y) x = ∑ j ∈ S, a j * deriv (f j) x :=
  fderiv_layer_sum S a f hf x 1

private theorem complexSplitOperator_layer_sum {β : Type*}
    (A : Matrix (I n) (I n) ℂ) (τ : ℂ) (c : I n → ℂ)
    (S : Finset β) (a : β → ℂ) (V : β → Y × ℝ → ℂ)
    (hV : ∀ j ∈ S, ContDiff ℝ ∞ (V j)) (y : Y) (t : ℝ) :
    complexSplitOperator A τ c (fun z => ∑ j ∈ S, a j * V j z) y t =
      ∑ j ∈ S, a j * complexSplitOperator A τ c (V j) y t := by
  let W (z : Y × ℝ) := ∑ j ∈ S, a j * V j z
  have hT (j) (hj : j ∈ S) : ContDiff ℝ ∞ (fun u : Y => V j (u,t)) :=
    (hV j hj).comp (contDiff_id.prodMk contDiff_const)
  have hN (j) (hj : j ∈ S) : ContDiff ℝ ∞ (fun r : ℝ => V j (y,r)) :=
    (hV j hj).comp (contDiff_const.prodMk contDiff_id)
  have hfirst (i : I n) (u : Y) : splitFirst W u t i =
      ∑ j ∈ S, a j * splitFirst (V j) u t i :=
    fderiv_layer_sum S a (fun j w => V j (w,t)) hT u _
  have hsecond (i l : I n) : splitSecond W y t i l =
      ∑ j ∈ S, a j * splitSecond (V j) y t i l := by
    change fderiv ℝ (fun u => splitFirst W u t l) y _ = _
    simp_rw [hfirst]
    apply fderiv_layer_sum
    intro j hj
    exact ((hT j hj).fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const
  have hnormal (s : ℝ) : splitNormal W y s = ∑ j ∈ S, a j * splitNormal (V j) y s :=
    deriv_layer_sum S a (fun j r => V j (y,r)) hN s
  have hnormalSecond : splitNormalSecond W y t = ∑ j ∈ S, a j * splitNormalSecond (V j) y t := by
    change deriv (fun s => splitNormal W y s) t = _
    simp_rw [hnormal]
    apply deriv_layer_sum
    intro j hj
    exact ((hN j hj).of_le (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).deriv'
  change complexSplitOperator A τ c W y t = _
  unfold complexSplitOperator
  simp only [hfirst,hsecond,hnormal,hnormalSecond,mul_sub,mul_add,mul_neg,mul_sum,sum_neg_distrib,
    sum_sub_distrib,sum_add_distrib]
  have hA :
      (∑ i : I n, ∑ l : I n, ∑ j ∈ S, A i l * (a j * splitSecond (V j) y t i l)) =
        ∑ j ∈ S, ∑ i : I n, ∑ l : I n, a j * (A i l * splitSecond (V j) y t i l) := by
    calc
      _ = ∑ i : I n, ∑ j ∈ S, ∑ l : I n, A i l * (a j * splitSecond (V j) y t i l) :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = ∑ j ∈ S, ∑ i : I n, ∑ l : I n, A i l * (a j * splitSecond (V j) y t i l) :=
        sum_comm
      _ = _ := by simp only [mul_left_comm]
  rw [hA]
  have hc :
      (∑ i : I n, ∑ j ∈ S, c i * (a j * splitFirst (V j) y t i)) =
        ∑ j ∈ S, ∑ i : I n, a j * (c i * splitFirst (V j) y t i) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  rw [hc]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j _
  ring

/-- The finite plane wave is the sum of its scaled, cutoff profiles. -/
theorem BoundaryLayerCoefficients.finiteWave_eq_layer_sum {ξ : I n → ℝ} {U : Set Y}
    (B : BoundaryLayerCoefficients ξ U) (a : Y → ℂ) (η : ℝ → ℝ) (M : ℕ) (h : ℝ) :
    B.finiteWave a η M h = fun z => ∑ j ∈ Finset.range (M + 1),
      (h ^ j : ℂ) * normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j)) z := by
  funext z
  unfold BoundaryLayerCoefficients.finiteWave
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [cutoffProfileFamily,normalCutoffWave,scaledPlaneWave,BoundaryLayerCoefficients.profile,
    polynomialProfileFamily,polynomialProfile,Complex.real_smul]
  ring

set_option maxHeartbeats 1000000 in
/-- The actual signed metric Laplacian applied to the finite wave has
the required uniform scaled residual on the physical collar. -/
theorem exists_signed_finiteWave_laplace_bound {O : Set Z} (hO : IsOpen O)
    (g : MetricField (n + 1)) (hg : CalderonN.SmoothMetric O g) (hN : HasNormalMetricBlock 0 g O)
    {U : Set Y} (hU : IsOpen U)
    (hFace : MapsTo (fun y : Y => signedLayerCoordinates (y,(0 : ℝ))) U O)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ))
    (hRect : K ×ˢ Icc 0 η.rOut ⊆ signedLayerCoordinates ⁻¹' O) (M : ℕ) :
    let B := boundaryLayerCoefficientsOfMetric hO g hg hFace ξ hξ
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ t ∈ Icc 0 η.rOut, ∀ h : ℝ, 0 < h → h ≤ 1 →
      let z := signedLayerCoordinates (y,t)
      let V := B.finiteWave a η M h
      ‖(h : ℂ) ^ 2 * (⟨-laplace g (Complex.reCLM ∘ V ∘ signedLayerCoordinates.symm) z,
        -laplace g (Complex.imCLM ∘ V ∘ signedLayerCoordinates.symm) z⟩ : ℂ)‖ ≤ C * h ^ (M + 1) := by
  let B := boundaryLayerCoefficientsOfMetric hO g hg hFace ξ hξ
  let A (w : Y × ℝ) : Matrix (I n) (I n) ℝ :=
    Matrix.of (fun i j => (g (signedLayerCoordinates w))⁻¹ i.succ j.succ)
  let τ (w : Y × ℝ) : ℝ := -2 * laplaceFirstCoeff g (signedLayerCoordinates w) 0
  let c (w : Y × ℝ) (i : I n) : ℝ := laplaceFirstCoeff g (signedLayerCoordinates w) i.succ
  have hKη : IsCompact (K ×ˢ Icc 0 η.rOut) := hK.prod isCompact_Icc
  have hτ : ContinuousOn τ (K ×ˢ Icc 0 η.rOut) :=
    ((contDiffOn_const.mul (contDiffOn_laplaceFirstCoeff hO hg 0)).continuousOn.comp
      signedLayerCoordinates.continuous.continuousOn hRect)
  obtain ⟨T,hT⟩ := hKη.exists_bound_of_continuousOn hτ
  obtain ⟨C,hC,hTaylor⟩ :=
    exists_native_layerCoefficientTaylor_bound hO g hg hFace ξ hξ hK η.rOut_pos hRect M
  have hE : LayerCoefficientTaylorError A τ c B K η.rOut M C :=
    fun z hz ht => hTaylor z.1 hz z.2 ht
  have hSymm (w : Y × ℝ) (hw : w.1 ∈ K) (ht : w.2 ∈ Icc 0 η.rOut) (i j : I n) :
      A w i j = A w j i :=
    congrFun (congrFun (hg.2 _ (hRect ⟨hw,ht⟩)).inv.isHermitian.isSymm j.succ) i.succ
  obtain ⟨C',hC',hBound⟩ := B.exists_cutoff_scalar_residual_bound A τ c hU hK hKU a ha ha0
    η M hC (le_max_left 0 T) hE hSymm
    (fun w hw ht => (by simpa only [Real.norm_eq_abs] using hT w ⟨hw,ht⟩ : |τ w| ≤ T).trans (le_max_right 0 T))
  refine ⟨C',hC',fun y hy t ht h hh hh1 => ?_⟩
  have hV := B.finiteWave_contDiff hU hK.isClosed hKU a ha ha0 η η.contDiff M h
  let W (j : ℕ) := normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j))
  have hW (j : ℕ) (_ : j ∈ Finset.range (M + 1)) : ContDiff ℝ ∞ (W j) :=
    contDiff_normalCutoffWave η.contDiff
      (contDiff_scaledPlaneWave ξ h (B.profile_contDiff hU hK.isClosed hKU a ha ha0 j))
  let z := signedLayerCoordinates (y,t)
  let V := B.finiteWave a η M h
  change ‖(h : ℂ) ^ 2 * (⟨-laplace g (Complex.reCLM ∘ V ∘ signedLayerCoordinates.symm) z,
    -laplace g (Complex.imCLM ∘ V ∘ signedLayerCoordinates.symm) z⟩ : ℂ)‖ ≤ C' * h ^ (M + 1)
  rw [← complexSplitOperator_eq_neg_laplace hO hg hN hV y t (hRect ⟨hy,ht⟩),
    B.finiteWave_eq_layer_sum a η M h,
    complexSplitOperator_layer_sum _ _ _ (Finset.range (M + 1)) (fun j => (h ^ j : ℂ)) W hW,
    mul_sum]
  simpa only [mul_left_comm,A,τ,c,W,Matrix.of_apply] using hBound (y,t) hy ht h hh hh1

end CalderonPatch.BoundaryLayer
