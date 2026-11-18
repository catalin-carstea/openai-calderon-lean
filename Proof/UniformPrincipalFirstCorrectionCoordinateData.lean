import Proof.PrincipalFirstCorrectionCoordinateWeights
import Proof.PrincipalFirstCorrectionCoordinateContraction
import Proof.PhysicalCorrectionCoframeData
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

/-- The actual bounded geometric correction in the first-base physical
    coefficient has genuine endpoints and small covariant bounds. The
    constant is fixed before every admitted radius and smooth frame. -/
theorem uniform_principal_first_correction_coordinate_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ b : I,
        ContDiffOn ℝ ∞ (fun x => principalFirstCorrectionCoordinateHalfL d x b) Y ∧
        ContDiffOn ℝ ∞ (fun x => principalFirstCorrectionCoordinateHigherL d x b) Y ∧ ∀ x ∈ Y,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
            (principalFirstCorrectionCoordinateHigherL d x b)=
              (principalFirstCorrectionCoordinateHalfL d x b).comp
                (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖principalFirstCorrectionCoordinateHalfL d x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ‖principalFirstCorrectionCoordinateHigherL d x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ∀ i : I,‖halfOperatorCovariantDerivativeL d
            (fun y => principalFirstCorrectionCoordinateHalfL d y b)
            (fun y => principalFirstCorrectionCoordinateHigherL d y b) x (axis i)‖ ≤ CE*ε := by
  classical
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let Q := physicalFirstCorrectionHalfBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let CE := 6*B*Q
  have hK0 := zero_lt_one.trans_le hK
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ hK0.le (abs_nonneg _)
  have hQ : 0 ≤ Q := physicalFirstCorrectionHalfBudget_nonneg _ _ _ _ _ hK0.le
  refine ⟨CE,mul_nonneg (mul_nonneg (by norm_num) hB) hQ,?_⟩
  intro floor hf ε hε hε1 d hd
  let Lo := fun (a : I) (x : X) => physicalFirstCorrectionHalfL d x (axis a)
  let Hi := fun (a : I) (x : X) => physicalFirstCorrectionHigherL d x (axis a)
  let w := fun (a b : I) => principalFirstErrorCoordinateWeight d a b
  let L := fun (b : I) (x : X) => ∑ a : I,w a b x • Lo a x
  let H := fun (b : I) (x : X) => ∑ a : I,w a b x • Hi a x
  have hData (a : I) := hd.physicalFirstCorrection_half_data hY hΩ hm hK hf hε hε1 a
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y := hd.contDiffOn_principalFirstErrorCoordinateWeight hK0 a b
  have hL (b : I) : ContDiffOn ℝ ∞ (L b) Y :=
    ContDiffOn.sum (fun a _ => (hWS a b).smul (hData a).1)
  have hH (b : I) : ContDiffOn ℝ ∞ (H b) Y :=
    ContDiffOn.sum (fun a _ => (hWS a b).smul (hData a).2.1)
  have hEq (b : I) (x : X) (hx : x ∈ Y) : principalFirstCorrectionCoordinateHalfL d x b=L b x :=
    principalFirstCorrectionCoordinateHalfL_eq d x (hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)) b
  have hBounds (b : I) (x : X) (hx : x ∈ Y) (i : I) :
      ‖L b x‖ ≤ CE*ε/beta d.γ d.radius x ∧ ‖H b x‖ ≤ CE*ε/beta d.γ d.radius x ∧
      ‖halfOperatorCovariantDerivativeL d (L b) (H b) x (axis i)‖ ≤ CE*ε := by
    have hw (a : I) := hd.principalFirstErrorCoordinateWeight_small_bounds hY (by omega) hK hf hε hε1 hx a b i
    exact half_small_weighted_combination_bounds d (fun a => w a b) Lo Hi x (axis i)
      (fun a => (hWS a b).contDiffAt (hY.mem_nhds hx))
      (fun a => (hData a).1.contDiffAt (hY.mem_nhds hx)) hB hQ hε
      (hf.trans (hd.2.2.2.2.1.2 x hx).2.1) (fun a => (hw a).1) (fun a => (hw a).2)
      (fun a => ((hData a).2.2 x hx).1) (fun a => ((hData a).2.2 x hx).2.1)
      (fun a => ((hData a).2.2 x hx).2.2 i)
  intro b
  refine ⟨(hL b).congr (fun x hx => hEq b x hx),hH b,?_⟩
  intro x hx
  have hPair := half_weighted_combination_balanced (fun a => w a b x)
    (fun a => Lo a x) (fun a => Hi a x) (fun a => physicalFirstCorrection_balanced d x (axis a))
  have hN := hBounds b x hx 0
  refine ⟨?_,?_,hN.2.1,?_⟩
  · rw [hEq b x hx]
    exact hPair
  · rw [hEq b x hx]
    exact hN.1
  · intro i
    have hGerm : (fun y => principalFirstCorrectionCoordinateHalfL d y b) =ᶠ[𝓝 x] L b := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact hEq b y hy
    change ‖halfOperatorCovariantDerivativeL d (fun y => principalFirstCorrectionCoordinateHalfL d y b)
      (H b) x (axis i)‖ ≤ CE*ε
    rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ (H b) x (axis i) hGerm]
    exact (hBounds b x hx i).2.2
end ShrinkingSpheres
