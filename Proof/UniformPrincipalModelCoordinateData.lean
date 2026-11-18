import Proof.PrincipalModelCoordinateContraction
import Proof.FramedRaisingHalfCovariantData
import Proof.HalfCovariantSmallScalarProduct
import Proof.HalfCovariantSmallWeightedCombination
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

def principalModelCoordinateHalfL (d : Data) (y : X) (b : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ j : I,d.frame y j b • principalModelFirstDerivativeHalfL d y j

def principalModelCoordinateHigherL (d : Data) (y : X) (b : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  principalModelDegreeCoordinateWeight d b y • degreeHigherL+
    ∑ a : I,principalModelRaisingCoordinateWeight d a b y • framedRaisingHigherL d y (axis a)

/-- Uniform genuine low/high and literal covariant derivative estimates
    for the complete model part of the first-base coordinate coefficient. -/
theorem uniform_principal_model_coordinate_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ b : I,
        ContDiffOn ℝ ∞ (fun x => principalModelCoordinateHalfL d x b) Y ∧
        ContDiffOn ℝ ∞ (fun x => principalModelCoordinateHigherL d x b) Y ∧ ∀ x ∈ Y,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
            (principalModelCoordinateHigherL d x b)=
              (principalModelCoordinateHalfL d x b).comp
                (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖principalModelCoordinateHalfL d x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ‖principalModelCoordinateHigherL d x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ∀ i : I,‖halfOperatorCovariantDerivativeL d
            (fun y => principalModelCoordinateHalfL d y b)
            (fun y => principalModelCoordinateHigherL d y b) x (axis i)‖ ≤ CE*ε := by
  classical
  let B := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let Q := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  let CD := 2*B*2
  let CR := 6*2*Q
  let CE := CD+CR
  have hK0 := zero_lt_one.trans_le hK
  have hB : 0 ≤ B := principalModelDegreeCoordinateBudget_nonneg _ _ _ hK0.le
  have hQ : 0 ≤ Q := framedRaisingHalfBudget_nonneg _ _ _ hK0.le
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  refine ⟨CE,add_nonneg hCD hCR,?_⟩
  intro floor hf ε hε hε1 d hd
  let LD := fun (b : I) (x : X) => principalModelDegreeCoordinateWeight d b x • degreeHalfL
  let HD := fun (b : I) (x : X) => principalModelDegreeCoordinateWeight d b x • degreeHigherL
  let LR := fun (b : I) (x : X) => ∑ a : I,principalModelRaisingCoordinateWeight d a b x • framedRaisingHalfL d x (axis a)
  let HR := fun (b : I) (x : X) => ∑ a : I,principalModelRaisingCoordinateWeight d a b x • framedRaisingHigherL d x (axis a)
  have hDS (b : I) := hd.contDiffOn_principalModelDegreeCoordinateWeight hY hK0 b
  have hRS (a b : I) := hd.contDiffOn_principalModelRaisingCoordinateWeight hK0 a b
  have hFS (a : I) := hd.framedRaisingHalf_smooth (axis a)
  have hLDS (b : I) : ContDiffOn ℝ ∞ (LD b) Y := (hDS b).smul contDiffOn_const
  have hHDS (b : I) : ContDiffOn ℝ ∞ (HD b) Y := (hDS b).smul contDiffOn_const
  have hLRS (b : I) : ContDiffOn ℝ ∞ (LR b) Y := ContDiffOn.sum (fun a _ => (hRS a b).smul (hFS a).1)
  have hHRS (b : I) : ContDiffOn ℝ ∞ (HR b) Y := ContDiffOn.sum (fun a _ => (hRS a b).smul (hFS a).2.1)
  have hEq (b : I) (x : X) (hx : x ∈ Y) : principalModelCoordinateHalfL d x b=LD b x+LR b x :=
    hd.principalModelFirstDerivative_coordinate_eq hY hx b
  have hND (b : I) (x : X) (hx : x ∈ Y) (i : I) :
      ‖LD b x‖ ≤ CD*ε/beta d.γ d.radius x ∧ ‖HD b x‖ ≤ CD*ε/beta d.γ d.radius x ∧
      ‖halfOperatorCovariantDerivativeL d (LD b) (HD b) x (axis i)‖ ≤ CD*ε := by
    have hw := hd.principalModelDegreeCoordinateWeight_bounds hY hm hK hf hε hε1 hx b i
    exact half_small_scalar_product_bounds d (principalModelDegreeCoordinateWeight d b)
      (fun _ => degreeHalfL) (fun _ => degreeHigherL) x (axis i)
      ((hDS b).contDiffAt (hY.mem_nhds hx)) contDiffAt_const hB (by norm_num) hε
      (hf.trans (hd.2.2.2.2.1.2 x hx).2.1) hw.1 hw.2
      (norm_sphereSobolevShiftedDegreeL_le_two _) (norm_sphereSobolevShiftedDegreeL_le_two _)
      (by rw [degreeHalf_covariant_derivative_zero,norm_zero];norm_num)
  have hNR (b : I) (x : X) (hx : x ∈ Y) (i : I) :
      ‖LR b x‖ ≤ CR*ε/beta d.γ d.radius x ∧ ‖HR b x‖ ≤ CR*ε/beta d.γ d.radius x ∧
      ‖halfOperatorCovariantDerivativeL d (LR b) (HR b) x (axis i)‖ ≤ CR*ε := by
    have hw (a : I) := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hx a b i
    have hF (a : I) := hd.framedRaisingHalf_covariant_data hY hΩ hm hK a x hx
    exact half_small_weighted_combination_bounds d (fun a => principalModelRaisingCoordinateWeight d a b)
      (fun a x => framedRaisingHalfL d x (axis a)) (fun a x => framedRaisingHigherL d x (axis a)) x (axis i)
      (fun a => (hRS a b).contDiffAt (hY.mem_nhds hx)) (fun a => (hFS a).1.contDiffAt (hY.mem_nhds hx))
      (by norm_num) hQ hε (hf.trans (hd.2.2.2.2.1.2 x hx).2.1)
      (fun a => (hw a).1) (fun a => (hw a).2) (fun a => (hF a).1) (fun a => (hF a).2.1)
      (fun a => (hF a).2.2 i)
  intro b
  have hLS := (hLDS b).add (hLRS b)
  refine ⟨hLS.congr (fun x hx => hEq b x hx),(hHDS b).add (hHRS b),?_⟩
  intro x hx
  have hND0 := hND b x hx 0
  have hNR0 := hNR b x hx 0
  have hPD := degreeHalf_balanced
  have hPR := half_weighted_combination_balanced (fun a => principalModelRaisingCoordinateWeight d a b x)
    (fun a => framedRaisingHalfL d x (axis a)) (fun a => framedRaisingHigherL d x (axis a))
    (fun a => framedRaisingHalf_balanced d x (axis a))
  refine ⟨?_,?_,?_,?_⟩
  · rw [hEq b x hx]
    change (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (HD b x+HR b x)=
      (LD b x+LR b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    have hDP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (HD b x)=
        (LD b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
      apply ContinuousLinearMap.ext
      intro u
      have hh := congrArg (fun v => principalModelDegreeCoordinateWeight d b x • v) (DFunLike.congr_fun hPD u)
      simpa only [HD,LD,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul] using hh
    have hRP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (HR b x)=
        (LR b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := hPR
    rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,hDP,hRP]

  · rw [hEq b x hx]
    exact (norm_add_le _ _).trans ((add_le_add hND0.1 hNR0.1).trans_eq (by dsimp only [CE];ring))
  · change ‖HD b x+HR b x‖ ≤ CE*ε/beta d.γ d.radius x
    exact (norm_add_le _ _).trans ((add_le_add hND0.2.1 hNR0.2.1).trans_eq (by dsimp only [CE];ring))
  · intro i
    have hGerm : (fun y => principalModelCoordinateHalfL d y b) =ᶠ[𝓝 x] (fun y => LD b y+LR b y) := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact hEq b y hy
    change ‖halfOperatorCovariantDerivativeL d (fun y => principalModelCoordinateHalfL d y b)
      (fun y => HD b y+HR b y) x (axis i)‖ ≤ CE*ε
    rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ _ x (axis i) hGerm,
      halfOperatorCovariantDerivativeL_add d (LD b) (LR b) (HD b) (HR b) x (axis i)
        ((hLDS b).contDiffAt (hY.mem_nhds hx)) ((hLRS b).contDiffAt (hY.mem_nhds hx))]
    exact (norm_add_le _ _).trans ((add_le_add (hND b x hx i).2.2 (hNR b x hx i).2.2).trans_eq
      (by dsimp only [CE];ring))
end ShrinkingSpheres
