import Proof.HalfCovariantWeightedCombination
import Proof.PrincipalFirstErrorCoordinateWeights
import Proof.FirstErrorCoordinateContraction
import Proof.UniformActualHalfCovariantErrorData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The actual first-error contribution to every fixed-coordinate
    principal first-base coefficient has a genuine higher endpoint and
    the two literal covariant Green bounds. Constants precede all admitted
    profiles and all already selected physical coefficient packages. -/
theorem uniform_principal_first_error_coordinate_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ Hi : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ b : I,
        ContDiffOn ℝ ∞ (fun x => P.first.principalFirstErrorCoordinateHalfL x b) Y ∧
        ContDiffOn ℝ ∞ (Hi b) Y ∧ ∀ x ∈ Y,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi b x)=
            (P.first.principalFirstErrorCoordinateHalfL x b).comp
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖P.first.principalFirstErrorCoordinateHalfL x b‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ‖Hi b x‖ ≤ CE*ε/beta d.γ d.radius x ∧
          ∀ i : I,‖halfOperatorCovariantDerivativeL d
            (fun y => P.first.principalFirstErrorCoordinateHalfL y b) (Hi b) x (axis i)‖ ≤ CE*ε := by
  classical
  obtain ⟨η,C0,C1,hη,hη1,hC0,hC1,hData⟩ := uniform_actual_first_error_half_covariant_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let Q := C0+C1
  let CE := 6*B*Q
  have hK0 := zero_lt_one.trans_le hK
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ hK0.le (abs_nonneg _)
  have hQ : 0 ≤ Q := add_nonneg hC0 hC1
  have hCE : 0 ≤ CE := mul_nonneg (mul_nonneg (by norm_num) hB) hQ
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hAxis (a : I) := hData floor hf ε hε hSmall d hd (axis a) P.radial P.adjoint (P.center a)
    P.adjoint_smooth (P.center_smooth a) P.radial_actual P.adjoint_pair (P.center_actual a)
  choose Lo Hi hLS hHS hAll using hAxis
  let w := fun (a b : I) => principalFirstErrorCoordinateWeight d a b
  let H := fun (b : I) (x : X) => ∑ a : I,w a b x • Hi a x
  let L := fun (b : I) (x : X) => ∑ a : I,w a b x • Lo a x
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y := hd.contDiffOn_principalFirstErrorCoordinateWeight hK0 a b
  have hLow (a : I) (x : X) (hx : x ∈ Y) := (hAll a x hx).1
  have hEq (b : I) (x : X) (hx : x ∈ Y) : P.first.principalFirstErrorCoordinateHalfL x b=L b x :=
    P.first.principalFirstErrorCoordinateHalfL_eq Lo hx
      (hd.1.2.2.2.2.2.2.2 x (hSub hx)) (fun a => hLow a x hx) b
  have hL (b : I) : ContDiffOn ℝ ∞ (L b) Y := ContDiffOn.sum (fun a _ => (hWS a b).smul (hLS a))
  have hH (b : I) : ContDiffOn ℝ ∞ (H b) Y := ContDiffOn.sum (fun a _ => (hWS a b).smul (hHS a))
  have hNorm (x : X) (hx : x ∈ Y) :
      (∀ a : I,‖Lo a x‖ ≤ Q*ε/beta d.γ d.radius x) ∧
      (∀ a : I,‖Hi a x‖ ≤ Q*ε/beta d.γ d.radius x) ∧
      (∀ a i : I,‖halfOperatorCovariantDerivativeL d (Lo a) (Hi a) x (axis i)‖ ≤ Q*ε) := by
    have hp := hd.2.2.2.2.1.2 x hx
    have hβ : 0 < beta d.γ d.radius x := zero_lt_one.trans_le (hf.trans hp.2.1)
    have hR := radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hp.1.le hf hp.2.1
      (hd.2.2.2.2.2 x hx).2
    have hr : d.radius x ≤ ε/beta d.γ d.radius x := (le_div_iff₀ hβ).mpr
      (hR.2.1.trans (div_le_self hε hf))
    have hC0Q : C0 ≤ Q := le_add_of_nonneg_right hC1
    have hC1Q : C1 ≤ Q := le_add_of_nonneg_left hC0
    have hRBound : C0*d.radius x ≤ Q*ε/beta d.γ d.radius x := by
      calc
        _ ≤ Q*d.radius x := mul_le_mul_of_nonneg_right hC0Q hp.1.le
        _ ≤ Q*(ε/beta d.γ d.radius x) := mul_le_mul_of_nonneg_left hr hQ
        _ = _ := by ring
    refine ⟨?_,?_,?_⟩
    · intro a
      have hh : ‖Lo a x‖ ≤ C0*d.radius x := by
        simpa only [norm_axis,mul_one] using (hAll a x hx).2.2.2.1
      exact hh.trans hRBound
    · intro a
      have hh : ‖Hi a x‖ ≤ C0*d.radius x := by
        simpa only [norm_axis,mul_one] using (hAll a x hx).2.2.2.2.1
      exact hh.trans hRBound
    · intro a i
      have hh := ((hAll a x hx).2.2.2.2.2 (axis i) (by simpa only [norm_axis] using (le_refl (1:ℝ)))).2
      have hh' : ‖halfOperatorCovariantDerivativeL d (Lo a) (Hi a) x (axis i)‖ ≤ C1*ε := by
        simpa only [norm_axis,mul_one] using hh
      exact hh'.trans (mul_le_mul_of_nonneg_right hC1Q hε)
  have hBounds (b : I) (x : X) (hx : x ∈ Y) (i : I) :
      ‖L b x‖ ≤ CE*ε/beta d.γ d.radius x ∧ ‖H b x‖ ≤ CE*ε/beta d.γ d.radius x ∧
      ‖halfOperatorCovariantDerivativeL d (L b) (H b) x (axis i)‖ ≤ CE*ε := by
    have hN := hNorm x hx
    have hw (a : I) := hd.principalFirstErrorCoordinateWeight_bounds hY (by omega) hK hf hε
      (hSmall.trans hη1) hx a b i
    exact half_weighted_combination_bounds d (fun a => w a b) Lo Hi x (axis i)
      (fun a => (hWS a b).contDiffAt (hY.mem_nhds hx)) (fun a => (hLS a).contDiffAt (hY.mem_nhds hx))
      hB hQ hε (zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 x hx).2.1))
      (fun a => (hw a).1) (fun a => (hw a).2) hN.1 hN.2.1 (fun a => hN.2.2 a i)
  refine ⟨H,?_⟩
  intro b
  refine ⟨(hL b).congr (fun x hx => hEq b x hx),hH b,?_⟩
  intro x hx
  have hPair := half_weighted_combination_balanced (fun a => w a b x)
    (fun a => Lo a x) (fun a => Hi a x) (fun a => (hAll a x hx).2.2.1)
  have hN := hBounds b x hx 0
  refine ⟨?_,?_,hN.2.1,?_⟩
  · rw [hEq b x hx]
    exact hPair
  · rw [hEq b x hx]
    exact hN.1
  · intro i
    have hGerm : (fun y => P.first.principalFirstErrorCoordinateHalfL y b) =ᶠ[𝓝 x] L b := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact hEq b y hy
    rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ (H b) x (axis i) hGerm]
    exact (hBounds b x hx i).2.2
end ShrinkingSpheres
