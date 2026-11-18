import Proof.ParallelFirstSelfErrorCoordinateAdjointPacket
import Proof.UniformActualFirstAdjointEndpoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The complete weighted native-error coordinate coefficient has a
fixed true-adjoint HIGH family and genuine HIGH first covariant jets with
the original epsilon norm. All choices precede tests and derivative directions. -/
theorem uniform_actual_error_coordinate_adjoint_jet_packet
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,Nonempty (FirstSelfCoordinateErrorAdjointPacket P CE ε) := by
  classical
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLow⟩ := uniform_actual_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hAdj⟩ := uniform_actual_error_adjoint_endpoint_family
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hNative⟩ := uniform_first_self_native_adjoint_packet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let CE := 3*B*(CA+CD)
  have hKpos := zero_lt_one.trans_le hK
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ hKpos.le (abs_nonneg _)
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  have hCA' : 3*B*CA ≤ CE := by
    dsimp only [CE]
    nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hB) hCD]
  refine ⟨min ηL (min ηA ηD),CE,lt_min hηL (lt_min hηA hηD),(min_le_left _ _).trans hηL1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hSmallL := hSmall.trans (min_le_left _ _)
  have hSmallA := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallD := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 := hSmallL.trans hηL1
  have hAxis (a : I) := hLow floor hf ε hε hSmallL d hd (axis a) P.radial P.adjoint (P.center a)
    P.radial_actual P.adjoint_pair (P.center_actual a)
  choose Lo Hi hLS hHS hAll using hAxis
  let p : (a : I) → FirstSelfActualErrorEndpointPacket Y d (axis a) := fun a =>
    { radial := P.radial
      adjoint := P.adjoint
      center := P.center a
      low := Lo a
      high := Hi a
      adjoint_smooth := P.adjoint_smooth
      center_smooth := P.center_smooth a
      low_smooth := hLS a
      radial_actual := P.radial_actual
      adjoint_actual := P.adjoint_pair
      center_actual := P.center_actual a
      low_graph := fun x hx => (hAll a x hx).1
      high_graph := fun x hx => (hAll a x hx).2.1 }
  have hA (a : I) := hAdj floor hf ε hε hSmallA d hd (axis a) (p a)
  choose AH hAH using hA
  let w := fun a b : I => principalFirstErrorCoordinateWeight d a b
  let H := fun (b : I) (x : X) => ∑ a : I,w a b x • AH a x
  let C := fun (b : I) (x : X) => ∑ a : I,w a b x • (Lo a x).adjoint
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y := hd.contDiffOn_principalFirstErrorCoordinateWeight hKpos a b
  have hAS (a : I) : ContDiffOn ℝ ∞ (fun x => (Lo a x).adjoint) Y := Adj.contDiff.comp_contDiffOn (hLS a)
  have hEq (b : I) (x : X) (hx : x ∈ Y) : (P.first.principalFirstErrorCoordinateHalfL x b).adjoint=C b x :=
    actual_error_coordinate_adjoint_eq P Lo hx (hd.1.2.2.2.2.2.2.2 x (hSub hx))
      (fun a => (hAll a x hx).1) b
  have hGraph (b : I) (y : X) (hy : y ∈ Y) :
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H b y)=
        (P.first.principalFirstErrorCoordinateHalfL y b).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    rw [hEq b y hy]
    exact half_weighted_combination_balanced (fun a => w a b y) (fun a => (Lo a y).adjoint)
      (fun a => AH a y) (fun a => (hAH a y hy).1)
  have hRadius (y : X) (hy : y ∈ Y) : d.radius y*beta d.γ d.radius y ≤ ε := by
    have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hPower : beta d.γ d.radius y ≤ (beta d.γ d.radius y)^2 := by nlinarith only [hβ]
    exact (mul_le_mul_of_nonneg_left hPower hr).trans (hd.2.2.2.2.2 y hy).2
  refine ⟨{ higher := H
            low_smooth := fun b => (ContDiffOn.sum (fun a _ => (hWS a b).smul (hAS a))).congr (hEq b)
            graph := hGraph
            norm := ?_
            jet := ?_ }⟩
  · intro b y hy
    have hβ : 0 < beta d.γ d.radius y := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
    have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
    have hAN (a : I) : ‖AH a y‖ ≤ CA*d.radius y := by
      simpa only [norm_axis,mul_one] using (hAH a y hy).2
    have hw (a : I) := hd.principalFirstErrorCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy a b 0
    calc
      _ ≤ 3*B*(CA*d.radius y) := norm_weighted_sum_three_le _ _ B _ hB (fun a => (hw a).1) hAN
      _ = (3*B*CA)*d.radius y := by ring
      _ ≤ CE*d.radius y := mul_le_mul_of_nonneg_right hCA' hr
      _ ≤ CE*(ε/beta d.γ d.radius y) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hβ).2 (hRadius y hy)) hCE
      _ = _ := by ring
  · intro b i y hy
    let q := fun a : I => Classical.choice (hNative floor hf ε hε hSmallD d hd y hy (axis a))
    have hAN (a : I) : ‖AH a y‖ ≤ CA*d.radius y := by
      simpa only [norm_axis,mul_one] using (hAH a y hy).2
    have hw (a : I) := hd.principalFirstErrorCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy a b i
    obtain ⟨T,hT,hTN⟩ := weighted_actual_error_true_adjoint_jet_at hY hΩ hSub hd hKpos hCA hCD hB hy
      (hf.trans (hd.2.2.2.2.1.2 y hy).2.1) p q AH (fun a => (hAH a y hy).1) hAN
      (fun a => w a b) (fun a => (hWS a b).contDiffAt (hY.mem_nhds hy)) i
      (fun a => (hw a).1) (fun a => (hw a).2)
    refine ⟨T,?_,?_⟩
    · have hGerm : (fun x => (P.first.principalFirstErrorCoordinateHalfL x b).adjoint)=ᶠ[𝓝 y] C b := by
        filter_upwards [hY.mem_nhds hy] with x hx
        exact hEq b x hx
      rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ (H b) y (axis i) hGerm]
      exact hT
    · change ‖T‖ ≤ CE*ε
      calc
        _ ≤ CE*d.radius y*beta d.γ d.radius y := hTN
        _ = CE*(d.radius y*beta d.γ d.radius y) := by ring
        _ ≤ CE*ε := mul_le_mul_of_nonneg_left (hRadius y hy) hCE

end ShrinkingSpheres.ParallelEnergy
