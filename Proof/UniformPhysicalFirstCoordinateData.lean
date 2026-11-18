import Proof.UniformPrincipalModelCoordinateData
import Proof.UniformPrincipalFirstCorrectionCoordinateData
import Proof.UniformPrincipalFirstErrorCoordinateData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The complete SAME physical first-base coefficient has genuine
    balanced endpoints and the literal covariant Green weights. All
    constants precede the admitted profiles, frames and selected P. -/
theorem uniform_physical_first_coordinate_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ Hi : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),∀ b : I,
        ContDiffOn ℝ ∞ (fun x => P.firstDerivativeCoordinateHalfL x b) Y ∧
        ContDiffOn ℝ ∞ (Hi b) Y ∧ ∀ x ∈ Y,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi b x)=
            (P.firstDerivativeCoordinateHalfL x b).comp
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖P.firstDerivativeCoordinateHalfL x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ‖Hi b x‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ∀ i : I,‖halfOperatorCovariantDerivativeL d
            (fun y => P.firstDerivativeCoordinateHalfL y b) (Hi b) x (axis i)‖ ≤ CE*ε := by
  obtain ⟨CM,hCM,hModel⟩ := uniform_principal_model_coordinate_data hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨CC,hCC,hCorr⟩ := uniform_principal_first_correction_coordinate_data hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨η,CFst,hη,hη1,hCFst,hError⟩ := uniform_principal_first_error_coordinate_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CE := CM+CC+CFst
  have hThree {V : Type} [SeminormedAddCommGroup V] (u v w : V) {a b c : ℝ}
      (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ c) : ‖u+v+w‖ ≤ a+b+c :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hu hv)) hw)
  refine ⟨η,CE,hη,hη1,add_nonneg (add_nonneg hCM hCC) hCFst,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 := hSmall.trans hη1
  have hMD := hModel floor hf ε hε hε1 d hd
  have hCD := hCorr floor hf ε hε hε1 d hd
  obtain ⟨EH,hED⟩ := hError floor hf ε hε hSmall d hd CF CT P
  let ML := fun (b : I) (x : X) => principalModelCoordinateHalfL d x b
  let MH := fun (b : I) (x : X) => principalModelCoordinateHigherL d x b
  let CL := fun (b : I) (x : X) => principalFirstCorrectionCoordinateHalfL d x b
  let CH := fun (b : I) (x : X) => principalFirstCorrectionCoordinateHigherL d x b
  let EL := fun (b : I) (x : X) => P.first.principalFirstErrorCoordinateHalfL x b
  let L := fun (b : I) (x : X) => ML b x+CL b x+EL b x
  let H := fun (b : I) (x : X) => MH b x+CH b x+EH b x
  have hEq (b : I) (x : X) : P.firstDerivativeCoordinateHalfL x b=L b x :=
    P.firstDerivativeCoordinateHalfL_correction_split x b
  have hLS (b : I) : ContDiffOn ℝ ∞ (L b) Y := ((hMD b).1.add (hCD b).1).add (hED b).1
  have hHS (b : I) : ContDiffOn ℝ ∞ (H b) Y := ((hMD b).2.1.add (hCD b).2.1).add (hED b).2.1
  refine ⟨H,?_⟩
  intro b
  refine ⟨(hLS b).congr (fun x _ => hEq b x),hHS b,?_⟩
  intro x hx
  have hM := (hMD b).2.2 x hx
  have hC := (hCD b).2.2 x hx
  have hE := (hED b).2.2 x hx
  refine ⟨?_,?_,?_,?_⟩
  · rw [hEq b x]
    change (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (MH b x+CH b x+EH b x)=
      (ML b x+CL b x+EL b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    have hMP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (MH b x)=
      (ML b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := hM.1
    have hCP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (CH b x)=
      (CL b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := hC.1
    have hEP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (EH b x)=
      (EL b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := hE.1
    rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp,ContinuousLinearMap.add_comp,hMP,hCP,hEP]
  · rw [hEq b x]
    exact (hThree _ _ _ hM.2.1 hC.2.1 hE.2.1).trans_eq (by dsimp only [CE] <;> ring)
  · exact (hThree _ _ _ hM.2.2.1 hC.2.2.1 hE.2.2.1).trans_eq (by dsimp only [CE] <;> ring)
  · intro i
    have hGerm : (fun y => P.firstDerivativeCoordinateHalfL y b) =ᶠ[𝓝 x] L b :=
      Eventually.of_forall (fun y => hEq b y)
    rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ (H b) x (axis i) hGerm]
    change ‖halfOperatorCovariantDerivativeL d (fun y => ML b y+CL b y+EL b y)
      (fun y => MH b y+CH b y+EH b y) x (axis i)‖ ≤ CE*ε
    rw [halfOperatorCovariantDerivativeL_add d (fun y => ML b y+CL b y) (EL b)
      (fun y => MH b y+CH b y) (EH b) x (axis i)
        (((hMD b).1.add (hCD b).1).contDiffAt (hY.mem_nhds hx)) ((hED b).1.contDiffAt (hY.mem_nhds hx)),
      halfOperatorCovariantDerivativeL_add d (ML b) (CL b) (MH b) (CH b) x (axis i)
        ((hMD b).1.contDiffAt (hY.mem_nhds hx)) ((hCD b).1.contDiffAt (hY.mem_nhds hx))]
    exact (hThree _ _ _ (hM.2.2.2 i) (hC.2.2.2 i) (hE.2.2.2 i)).trans_eq (by dsimp only [CE] <;> ring)
end ShrinkingSpheres
