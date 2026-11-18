import Proof.ParallelNormAssemblyReservedHigherBridge
import Proof.ParallelNormAssemblyReservedCoordinateError
import Proof.ParallelNormAssemblyReservedNormalizedWords
import Proof.ParallelNormAssemblyReservedRadiusJets
import Proof.NativeCovariantHigherJet
import Proof.CovariantRotationGraphOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coordinate_error_high_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (a : I) :
    ContDiffOn ℝ ∞ (fun y => potentialCoordinateGeneratorHigh P y (.inr (.inr a))) Y := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have hc (j : I) : ContDiffOn ℝ ∞ (fun y => frameCoordinateLinear d.γ d.frame y j (axis a)) Y := by
    simpa only [frameCoordinateLinear_apply] using
      (hd.1.1.contDiffOn_metricPair (fun _ => axis a) (fun y => d.frame y j)
        contDiffOn_const (hd.1.2.2.2.2.2.2.1 j)).mono hSub
  exact ContDiffOn.sum (fun j _ => (hc j).smul (P.first.high_smooth j))

/-- Reuse of the EXISTING native forward HIGH first endpoint, normalized
by the actual radius and aligned to ANY selected genuine normalized coarse
first family. No new native family or second HIGH premise is introduced. -/
theorem uniform_normalized_coordinate_error_covariant_higher_first {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,∀ a : I,
    ∀ S : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    (∀ i y,y ∈ Y → CoarseCovariantRotationGraph d y (axis i)
      (fun x => (d.radius x)⁻¹ • actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x) (S i y)) →
    ∀ i : I,∀ y ∈ Y,∃ N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp N=
        (S i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
      higherOperatorCovariantDerivativeL d
        (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inr a))) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖N‖ ≤ C*beta d.γ d.radius y := by
  obtain ⟨η,C0,C1,hη,hη1,hC0,hC1,hHigh⟩ := uniform_actual_first_error_covariant_higher_graph
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CI,hCI,hInv⟩ := uniform_radius_inverse_two_jet_weights hY hSub (by omega) K ρ c₀ M Cj hK
  let C := C1+CI*C0
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P a S hS i y hy
  obtain ⟨H0,H1,T,h0,hT,h1,hH0,hH1,hHε⟩ := hHigh floor hf ε hε hSmall d hd
    P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
    (P.center a) (P.center_smooth a) (P.center_actual a) y hy (axis i) (by simp only [norm_axis];rfl)
  let w := fun x => (d.radius x)⁻¹
  let E := actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)
  let N := w y • H1+coordDeriv i w y • H0
  have hw : ContDiffOn ℝ ∞ w Y := hd.2.2.2.2.1.1.inv (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hES : ContDiffOn ℝ ∞ E Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1)
      P.adjoint (P.center a) P.adjoint_smooth (P.center_smooth a)
  have hScaled := hT.smul w ((hw.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hES.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hSame : S i y=w y • T+coordDeriv i w y • E y :=
    coarseCovariantRotationGraph_unique (hS i y hy) hScaled
  have hN : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp N=
      (S i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [hSame]
    apply ContinuousLinearMap.ext
    intro u
    have h0u := DFunLike.congr_fun h0 u
    have h1u := DFunLike.congr_fun h1 u
    simp only [ContinuousLinearMap.comp_apply] at h0u h1u
    simp only [N,E,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.smul_apply,map_add,map_smul,h0u,h1u]
  have hHS : ContDiffOn ℝ ∞ (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inr a))) Y :=
    hw.smul (coordinate_error_high_smooth P hd a)
  have hBase : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (normalizedPotentialGeneratorHigh P x (.inr (.inr a)))=
      (w x • E x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    apply ContinuousLinearMap.ext
    intro u
    have hh := DFunLike.congr_fun (coordinate_error_high_coarse P hx (hd.1.2.2.2.2.2.2.2 x (hSub hx)) a) u
    simp only [ContinuousLinearMap.comp_apply] at hh
    simpa only [normalizedPotentialGeneratorHigh,potentialGeneratorWeight,w,E,ContinuousLinearMap.comp_apply,
      _root_.smul_apply,map_smul] using congrArg (fun z => (d.radius x)⁻¹ • z) hh
  refine ⟨N,hN,higher_covariant_derivative_of_coarse (fun x => w x • E x)
    (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inr a))) (S i y) N
    (((hw.smul hES).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hBase (hS i y hy) hN,?_⟩
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
  have hh0 : ‖H0‖ ≤ C0*d.radius y := by simpa only [norm_axis,mul_one] using hH0
  have hh1 : ‖H1‖ ≤ C1*d.radius y*beta d.γ d.radius y := by simpa only [norm_axis,mul_one] using hH1
  have hI := (hInv floor hf ε d hd y hy).1 i
  have hN0 : ‖w y • H1‖ ≤ (d.radius y)⁻¹*(C1*d.radius y*beta d.γ d.radius y) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (by dsimp only [w];rw [abs_of_pos (inv_pos.mpr hr)]) hh1 (norm_nonneg _) (inv_nonneg.mpr hr.le)
  have hN1 : ‖coordDeriv i w y • H0‖ ≤ (CI*beta d.γ d.radius y/d.radius y)*(C0*d.radius y) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hI hh0 (norm_nonneg _) (by positivity)
  exact ((norm_add_le _ _).trans (add_le_add hN0 hN1)).trans_eq (by dsimp only [C];field_simp <;> ring)

end ShrinkingSpheres.ParallelEnergy
