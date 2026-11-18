import Proof.ParallelNormAssemblyReservedCoordinateOperators
import Proof.ParallelScalarFirstNativeStrongPacket
import Proof.CovariantHalfCoarseBridge

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

private lemma inverse_frame_coordinate_combination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (F : I → E) (a : I) :
    (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • (∑ b : I,d.frame y j b • F b))=F a := by
  have hDual (b : I) : (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a)*d.frame y j b)=
      if a=b then 1 else 0 := by
    have hh := congrArg (fun v : X => v b) (frameCoordinateLinear_reconstruct d.γ d.frame y (axis a) he)
    simpa only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,axis,PiLp.single_apply,eq_comm] using hh
  have hEq : (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • (∑ b : I,d.frame y j b • F b))=
      ∑ b : I,(∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a)*d.frame y j b) • F b := by
    simp only [Fin.sum_univ_three,smul_add,smul_smul,add_smul]
    module
  rw [hEq]
  simp [hDual]

lemma coordinate_error_coarse_reconstruction {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (a : I) :
    (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) •
      actualFrameFirstAdjointErrorFamily d P.adjoint P.center j y)=
      actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) y :=
  inverse_frame_coordinate_combination d y he
    (fun b => actualFirstAdjointErrorFamily d (axis b) P.adjoint (P.center b) y) a

/-- The coordinate potential generator retains the genuine actual native
axis-error coarse/half square, after cancelling the complete moving frame. -/
lemma coordinate_error_low_coarse {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (a : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) y)=
      (potentialCoordinateGeneratorLow P y (.inr (.inr a))).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  rw [← coordinate_error_coarse_reconstruction P y he a]
  apply ContinuousLinearMap.ext
  intro u
  simp only [potentialCoordinateGeneratorLow,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => frameCoordinateLinear d.γ d.frame y j (axis a) • z)
    (DFunLike.congr_fun (P.first.low_coarse j y hy) u)

lemma coordinate_error_high_coarse {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (a : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (potentialCoordinateGeneratorHigh P y (.inr (.inr a)))=
      (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) y).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  rw [← coordinate_error_coarse_reconstruction P y he a]
  apply ContinuousLinearMap.ext
  intro u
  simp only [potentialCoordinateGeneratorHigh,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => frameCoordinateLinear d.γ d.frame y j (axis a) • z)
    (DFunLike.congr_fun (P.first.high_coarse j y hy) u)

lemma coordinate_error_low_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (a : I) :
    ContDiffOn ℝ ∞ (fun y => potentialCoordinateGeneratorLow P y (.inr (.inr a))) Y := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have hc (j : I) : ContDiffOn ℝ ∞ (fun y => frameCoordinateLinear d.γ d.frame y j (axis a)) Y := by
    simpa only [frameCoordinateLinear_apply] using
      (hd.1.1.contDiffOn_metricPair (fun _ => axis a) (fun y => d.frame y j)
        contDiffOn_const (hd.1.2.2.2.2.2.2.1 j)).mono hSub
  exact ContDiffOn.sum (fun j _ => (hc j).smul (P.first.low_smooth j))

/-- The native strong-half two-jet producer is reused for the SAME actual
coordinate error generators; no new native endpoint construction occurs. -/
theorem uniform_coordinate_error_strong_half_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 C2 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,
    ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    ∃ L : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∀ a i : I,ContDiffOn ℝ ∞ (S a i) Y ∧ ContDiffOn ℝ ∞ (L a i) Y ∧ ∀ y ∈ Y,
      halfOperatorCovariantDerivativeL d
        (fun x => potentialCoordinateGeneratorLow P x (.inr (.inr a)))
        (fun x => potentialCoordinateGeneratorHigh P x (.inr (.inr a))) y (axis i)=
        (L a i y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖L a i y‖ ≤ C1*d.radius y*beta d.γ d.radius y ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S a i y)=
        (L a i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      CoarseCovariantRotationGraph d y (axis i)
        (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)) (S a i y) ∧
      ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y (axis j) (S a i) T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ C2*d.radius y*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨η,C1,C2,hη,hη1,hC1,hC2,hProduce⟩ := uniform_actual_first_error_strong_half_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C1,C2,hη,hη1,hC1,hC2,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  choose S L hJets using fun a : I => hProduce floor hf ε hε hSmall d hd
    P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
    (P.center a) (P.center_smooth a) (P.center_actual a)
  refine ⟨S,L,?_⟩
  intro a i
  refine ⟨(hJets a i).1,(hJets a i).2.1,?_⟩
  intro y hy
  have hJ := (hJets a i).2.2 y hy
  have he := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hES : ContDiffOn ℝ ∞ (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1)
      P.adjoint (P.center a) P.adjoint_smooth (P.center_smooth a)
  have hLow := coordinate_error_low_smooth P hd a
  have hStrong := halfOperatorCovariantDerivativeL_eq_strong_extension
    (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a))
    (fun x => potentialCoordinateGeneratorLow P x (.inr (.inr a)))
    (fun x => potentialCoordinateGeneratorHigh P x (.inr (.inr a)))
    (S a i y) (L a i y)
    ((hES.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hLow.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (by
      filter_upwards [hY.mem_nhds hy] with x hx
      exact coordinate_error_low_coarse P hx (hd.1.2.2.2.2.2.2.2 x (hSub hx)) a)
    (coordinate_error_high_coarse P hy he a) hJ.1 hJ.2.1
  refine ⟨hStrong,?_,hJ.2.1,hJ.1,?_⟩
  · simpa only [norm_axis,mul_one] using hJ.2.2.1
  · intro j
    obtain ⟨T,N,hT,hN,hNN⟩ := hJ.2.2.2 j
    exact ⟨T,N,hT,hN,by simpa only [norm_axis,mul_one] using hNN⟩

end ShrinkingSpheres.ParallelEnergy
