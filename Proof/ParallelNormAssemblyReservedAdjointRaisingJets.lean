import Proof.ParallelScalarModelRaising
import Proof.ParallelNormAssemblyReservedHigherApply
import Proof.UniformFlatRaisingConstantAdjointHigher
import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

structure RaisingAdjointFirstJets (Y : Set X) (d : Data) (C0 C1 : ℝ) where
  high : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  smooth : ∀ a,ContDiffOn ℝ ∞ (high a) Y
  balanced : ∀ a y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (high a y)=
      (framedRaisingHalfL d y (axis a)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  norm_bound : ∀ a y,y ∈ Y → ‖high a y‖ ≤ C0
  jet : ∀ a y,y ∈ Y → ∀ i : I,
    ∃ N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      higherOperatorCovariantDerivativeL d (high a) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖N‖ ≤ C1*beta d.γ d.radius y

/-- The true raising adjoint has a genuine first HIGH jet. Its coframe
and connection derivatives cancel to reference Christoffel coefficients;
the constant flat adjoints are the existing baseline selected witnesses. -/
theorem uniform_raising_adjoint_higher_first_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (RaisingAdjointFirstJets Y d C0 C1) := by
  obtain ⟨η,CR,hη,hη1,hCR,hFlat⟩ := uniform_flat_raising_constant_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let G := 9*K*|M ⟨1,by omega⟩|
  let C0 := 3*K*CR
  let C1 := 3*G*C0
  have hK0 := zero_le_one.trans hK
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hC0 : 0 ≤ C0 := by dsimp only [C0];positivity
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  refine ⟨η,C0,C1,hη,hη1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨A,hA⟩ := hFlat floor hf ε hε hSmall d hd CF CT P
  let AH := scalarModelRaisingAdjointHigher A d
  have hB (a : I) (y : X) (hy : y ∈ Y) :=
    scalarModelRaisingAdjointHigher_balanced A d a y (fun j => (hA y hy j).1)
  have hS (a : I) : ContDiffOn ℝ ∞ (AH a) Y := by
    apply ContDiffOn.sum
    intro j _
    have hc : ContDiffOn ℝ ∞ (fun x => frameCoordinateLinear d.γ d.frame x j (axis a)) Y := by
      simpa only [frameCoordinateLinear_apply] using
        ((hd.1.1.contDiffOn_metricPair (fun _ => axis a) (fun x => d.frame x j)
          contDiffOn_const (hd.1.2.2.2.2.2.2.1 j)).mono hSub)
    exact hc.smul (contDiffOn_const (c:=A j))
  have hNorm (a : I) (y : X) (hy : y ∈ Y) : ‖AH a y‖ ≤ C0 := by
    apply norm_weighted_sum_three_le _ _ K CR hK0
    · intro j
      rw [frameCoordinateLinear_apply]
      exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hSub hy) (hd.1.2.2.2.2.2.2.2 y (hSub hy)) a j
    · intro j
      exact (hA y hy j).2
  refine ⟨{ high := AH,smooth := hS,balanced := hB,norm_bound := hNorm,jet := ?_ }⟩
  intro a y hy i
  let N := ∑ b : I,christoffel d.γ y b i a • AH b y
  have hNGraph : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp N=
      (framedRaisingFirstHalfJet d i a y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(framedRaisingFirstHalfJet d i a y).adjoint_inner_left]
    simp only [N,framedRaisingFirstHalfJet,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
      sum_inner,inner_sum,real_inner_smul_left,inner_smul_right]
    apply Finset.sum_congr rfl
    intro b _
    have hb := DFunLike.congr_fun (hB b y hy) u
    simp only [ContinuousLinearMap.comp_apply] at hb
    exact congrArg (fun t => christoffel d.γ y b i a*t)
      ((congrArg (fun z => ⟪z,v⟫_ℝ) hb).trans ((framedRaisingHalfL d y (axis b)).adjoint_inner_left _ _))
  have hDR := framed_raising_strong_half_graph hY hΩ hd (zero_lt_one.trans_le hK) hy i a
  have hDA := half_covariant_adjoint_strong_extension d (fun x => framedRaisingHalfL d x (axis a))
    (fun x => framedRaisingHigherL d x (axis a)) (AH a)
    (((hd.framedRaisingHalf_smooth (axis a)).1).contDiffAt (hY.mem_nhds hy)) (axis i)
    (framedRaisingHalf_balanced d y (axis a)) (hB a y hy) (framedRaisingFirstHalfJet d i a y) hDR
  have hHH := higher_covariant_derivative_eq_half d
    (fun x => (framedRaisingHalfL d x (axis a)).adjoint) (AH a) y (axis i)
    ((scalarModelRaisingAdjoint_smooth hd a).contDiffAt (hY.mem_nhds hy))
    ((hS a).contDiffAt (hY.mem_nhds hy))
    (by filter_upwards [hY.mem_nhds hy] with x hx;exact hB a x hx)
  refine ⟨N,?_,?_⟩
  · rw [hDA,←hNGraph,ContinuousLinearMap.comp_assoc] at hHH
    exact hHH
  · have hGamma (b : I) : |christoffel d.γ y b i a| ≤ G :=
      hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) _ (abs_nonneg _)
        (fun b c => (hd.1.reference_fderiv_bound (by omega) (hSub hy) b c).trans (le_abs_self _)) b i a
    have hNN : ‖N‖ ≤ C1 := norm_weighted_sum_three_le _ _ G C0 hG hGamma (fun b => hNorm b y hy)
    exact hNN.trans (le_mul_of_one_le_right hC1 (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))

end ShrinkingSpheres.ParallelEnergy
