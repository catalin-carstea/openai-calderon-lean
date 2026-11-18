import Proof.ParallelNormAssemblyReservedNormalizeGraphs
import Proof.ParallelNormAssemblyReservedCoordinateError
import Proof.ParallelNormAssemblyReservedNormalizedWords

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual normalized coordinate native errors have ONE smooth low
first-jet family, genuine coarse/half second squares, and fixed/beta/
beta-squared norms. The producer is selected before every test. -/
theorem uniform_normalized_coordinate_error_strong_half_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CN1 CN2 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CN1 ∧ 0 ≤ CN2 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,
    ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    ∃ L : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∀ a i : I,ContDiffOn ℝ ∞ (S a i) Y ∧ ContDiffOn ℝ ∞ (L a i) Y ∧ ∀ y ∈ Y,
      halfOperatorCovariantDerivativeL d
        (fun x => normalizedPotentialGeneratorLow P x (.inr (.inr a)))
        (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inr a))) y (axis i)=
        (L a i y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖L a i y‖ ≤ CN1*beta d.γ d.radius y ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S a i y)=
        (L a i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      CoarseCovariantRotationGraph d y (axis i)
        (fun x => (d.radius x)⁻¹ • actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x)
        (S a i y) ∧
      ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y (axis j) (S a i) T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ CN2*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨η,C1,C2,hη,hη1,hC1,hC2,hJets⟩ := uniform_coordinate_error_strong_half_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CI,hCI,hInv⟩ := uniform_radius_inverse_two_jet_weights hY hSub (by omega) K ρ c₀ M Cj hK
  let C0 := 3*K*|CF|
  let CN1 := C1+CI*C0
  let CN2 := C2+2*CI*C1+CI*C0
  have hK0 := zero_le_one.trans hK
  have hC0 : 0 ≤ C0 := by dsimp only [C0];positivity
  refine ⟨η,CN1,CN2,hη,hη1,by dsimp only [CN1];positivity,by dsimp only [CN2];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨S,L,hSL⟩ := hJets floor hf ε hε hSmall d hd CF CT P
  let w := fun x => (d.radius x)⁻¹
  let E := fun a => actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)
  let EL := fun a x => potentialCoordinateGeneratorLow P x (.inr (.inr a))
  let EH := fun a x => potentialCoordinateGeneratorHigh P x (.inr (.inr a))
  have hw : ContDiffOn ℝ ∞ w Y := hd.2.2.2.2.1.1.inv (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1)
      P.adjoint (P.center a) P.adjoint_smooth (P.center_smooth a)
  have hELS (a : I) : ContDiffOn ℝ ∞ (EL a) Y := coordinate_error_low_smooth P hd a
  have hNorm0 (a : I) (y : X) (hy : y ∈ Y) : ‖EL a y‖ ≤ C0*d.radius y := by
    have he := hd.1.2.2.2.2.2.2.2 y (hSub hy)
    have hr := (hd.2.2.2.2.1.2 y hy).1
    have hc (j : I) : |frameCoordinateLinear d.γ d.frame y j (axis a)| ≤ K := by
      rw [frameCoordinateLinear_apply]
      exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hSub hy) he a j
    have hL (j : I) : ‖P.first.low j y‖ ≤ |CF| * d.radius y :=
      (P.first.low_bound j y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self CF) hr.le)
    exact (norm_weighted_sum_three_le _ _ K (|CF| * d.radius y) hK0 hc hL).trans_eq (by dsimp only [C0];ring)
  have hAll (a : I) := radius_normalized_coarse_half_two_jet_graph hY d w hw (E a) (EL a) (EH a) (S a) (L a)
    (hES a) (hELS a) (fun i => (hSL a i).1) (fun i => (hSL a i).2.1)
    (fun x hx => coordinate_error_low_coarse P hx (hd.1.2.2.2.2.2.2.2 x (hSub hx)) a)
    (fun i x hx => ((hSL a i).2.2 x hx).2.2.2.1)
    (fun i x hx => ((hSL a i).2.2 x hx).2.2.1)
    (fun i x hx => ((hSL a i).2.2 x hx).1)
  refine ⟨(fun a => normalizedCoarseFirstJet w (E a) (S a)),
    (fun a => normalizedHalfFirstJet w (EL a) (L a)),?_⟩
  intro a i
  refine ⟨((hAll a).1 i).1,((hAll a).1 i).2,?_⟩
  intro y hy
  have hN := (hAll a).2 y hy i
  have hJ := (hSL a i).2.2 y hy
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
  obtain ⟨hInv1,hInv2⟩ := hInv floor hf ε d hd y hy
  have hNorm (j : I) (N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
      (hNN : ‖N‖ ≤ C2*d.radius y*(beta d.γ d.radius y)^2) :=
    radius_normalized_two_jet_norms (EL a y) (L a i y) (L a j y) N
      (w y) (coordDeriv i w y) (coordDeriv j w y) (coordDeriv j (coordDeriv i w) y)
      C0 C1 C2 CI (d.radius y) (beta d.γ d.radius y) hC0 hC1 hC2 hCI hr hβ
      (by dsimp only [w];rw [abs_of_pos (inv_pos.mpr hr)]) (hInv1 i) (hInv1 j) (hInv2 j i)
      (hNorm0 a y hy) hJ.2.1 ((hSL a j).2.2 y hy).2.1 hNN
  obtain ⟨T0,N0,hT0,hN0,hNN0⟩ := hJ.2.2.2.2 0
  refine ⟨?_,(hNorm 0 N0 hNN0).2.1,hN.2.1,hN.1,?_⟩
  · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight] using hN.2.2.1
  · intro j
    obtain ⟨T,N,hT,hNN,hBound⟩ := hJ.2.2.2.2 j
    have hSquare := hN.2.2.2 j T N hT hNN
    refine ⟨_,_,hSquare.1,hSquare.2,(hNorm j N hBound).2.2⟩

end ShrinkingSpheres.ParallelEnergy
