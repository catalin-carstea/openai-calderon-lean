import Proof.ParallelNormAssemblyReservedAdjointCoordinateJets
import Proof.ParallelNormAssemblyReservedHigherScalarJets
import Proof.ParallelNormAssemblyReservedRadiusJets
import Proof.ParallelNormAssemblyReservedNormalizedWords

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

structure NormalizedErrorAdjointFirstJets {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (C0 C1 : ℝ) where
  high : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  smooth : ∀ a,ContDiffOn ℝ ∞ (high a) Y
  balanced : ∀ a y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (high a y)=
      (normalizedPotentialGeneratorLow P y (.inr (.inr a))).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  norm_bound : ∀ a y,y ∈ Y → ‖high a y‖ ≤ C0
  jet : ∀ a y,y ∈ Y → ∀ i : I,
    ∃ N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      higherOperatorCovariantDerivativeL d (high a) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖N‖ ≤ C1*beta d.γ d.radius y

private lemma radius_normalized_first_jet_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F N : E) (w wi C0 C1 CI r β : ℝ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
    (hr : 0 < r) (hβ : 0 ≤ β) (hw : |w| ≤ r⁻¹) (hwi : |wi| ≤ CI*β/r)
    (hF : ‖F‖ ≤ C0*r) (hN : ‖N‖ ≤ C1*r*β) :
    ‖w • F‖ ≤ C0 ∧ ‖wi • F+w • N‖ ≤ (C1+CI*C0)*β := by
  have hZ : |(0:ℝ)| ≤ CI*β^2/r := by rw [abs_zero];positivity
  have hT : ‖(0:E)‖ ≤ (0:ℝ)*r*β^2 := by simp only [norm_zero,zero_mul,le_refl]
  have hh := radius_normalized_two_jet_norms F N N (0:E) w wi wi 0 C0 C1 0 CI r β
    hC0 hC1 (le_refl 0) hCI hr hβ hw hwi hwi hZ hF hN hN hT
  exact ⟨hh.1,by simpa only [add_comm] using hh.2.1⟩

/-- Radius normalization preserves the SAME true-adjoint HIGH family,
with genuine first HIGH covariant jet C beta. Only native FIRST jets and
original inverse-radius profile derivatives are used. -/
theorem uniform_normalized_coordinate_error_adjoint_first_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (NormalizedErrorAdjointFirstJets P C0 C1) := by
  obtain ⟨η,C0,C1,hη,hη1,hC0,hC1,hRaw⟩ := uniform_coordinate_error_adjoint_higher_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CI,hCI,hInv⟩ := uniform_radius_inverse_two_jet_weights hY hSub (by omega) K ρ c₀ M Cj hK
  refine ⟨η,C0,C1+CI*C0,hη,hη1,hC0,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨A⟩ := hRaw floor hf ε hε hSmall d hd CF CT P
  let w := fun x => (d.radius x)⁻¹
  let AH := fun a x => w x • A.high a x
  have hw : ContDiffOn ℝ ∞ w Y := hd.2.2.2.2.1.1.inv (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  let Adj := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))))
  have hLow (a : I) : ContDiffOn ℝ ∞ (fun x => (potentialCoordinateGeneratorLow P x (.inr (.inr a))).adjoint) Y :=
    Adj.contDiff.comp_contDiffOn (coordinate_error_low_smooth P hd a)
  refine ⟨{ high := AH,smooth := ?_,balanced := ?_,norm_bound := ?_,jet := ?_ }⟩
  · intro a
    exact hw.smul (A.smooth a)
  · intro a y hy
    simp only [AH,normalizedPotentialGeneratorLow,potentialGeneratorWeight,w,
      ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,map_smul,A.balanced a y hy]
  · intro a y hy
    have hr := (hd.2.2.2.2.1.2 y hy).1
    calc
      _ = |w y| *‖A.high a y‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ |w y| *(C0*d.radius y) := mul_le_mul_of_nonneg_left (A.norm_bound a y hy) (abs_nonneg _)
      _ = _ := by dsimp only [w];rw [abs_of_pos (inv_pos.mpr hr)];field_simp
  · intro a y hy i
    obtain ⟨N,hN,hNN⟩ := A.jet a y hy i
    let NH := fderiv ℝ w y (axis i) • A.high a y+w y • N
    have hr := (hd.2.2.2.2.1.2 y hy).1
    have hI := (hInv floor hf ε d hd y hy).1 i
    have hBounds := radius_normalized_first_jet_norm (A.high a y) N (w y) (fderiv ℝ w y (axis i))
      C0 C1 CI (d.radius y) (beta d.γ d.radius y) hC0 hC1 hCI hr (Real.sqrt_nonneg _)
      (by dsimp only [w];rw [abs_of_pos (inv_pos.mpr hr)]) hI (A.norm_bound a y hy) hNN
    refine ⟨NH,?_,hBounds.2⟩
    exact weighted_higher_covariant_jet_graph d w
      (fun x => (potentialCoordinateGeneratorLow P x (.inr (.inr a))).adjoint) (A.high a) y (axis i)
      (hw.contDiffAt (hY.mem_nhds hy)) ((hLow a).contDiffAt (hY.mem_nhds hy))
      ((A.smooth a).contDiffAt (hY.mem_nhds hy))
      (by filter_upwards [hY.mem_nhds hy] with x hx;exact A.balanced a x hx) N hN

end ShrinkingSpheres.ParallelEnergy
