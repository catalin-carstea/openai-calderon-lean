import Proof.ParallelModelFirstLeadingPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

private lemma model_first_hodge_scale (μ g x h c : ℝ) (hx : x=h+c) :
    μ*(g*x)-(μ*g)*h=(μ*g)*c := by rw [hx];ring

/-- Exact six-term correction between the actual crossed leading rows
and their mixed Hodge derivatives. The B-adjoint jet is the SAME WF jet. -/
lemma modelFirstJetDensity_eq_rows
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y) :
    modelFirstJetDensity P WF W U y=
      ∑ k : I,∑ c : I,∑ b : I,modelFirstLeadingWeight d k c y*modelFirstExchangeJetCorrection
        (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y)
        (WF.covariantCoordinateAdjointHigher b y)
        (fiveHalfCovariantDerivative d U (axis k) y) (fiveHalfCovariantDerivative d U (axis b) y)
        (modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c k y
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))
        (modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c b y
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))
        (firstSelfAdjointSourceJetError P WF W U b k y) (firstSelfAdjointSourceJetError P WF W U b b y) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let U3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let H := fun i : I => fiveHalfCovariantDerivative d U (axis i) y
  let RA := fun c : I => scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y
  let BA := fun b : I => WF.covariantCoordinateAdjointHigher b y
  let r := fun c i : I => modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c i y U3
  let s := fun b i : I => firstSelfAdjointSourceJetError P WF W U b i y
  have hDR (c i : I) := model_first_raising_adjoint_source_product hY hΩ hd hK Q hQ
    modelFirstFlatAdjointHigher modelFirstFlatAdjointHigher_graph U hU hy c i
  have hDB (b i : I) : firstSelfAdjointSourceDerivative P WF W U b i y=BA b (H i)+s b i := by
    dsimp only [s,firstSelfAdjointSourceJetError,BA,H,firstSelfSourceDerivative,fiveHalfCovariantDerivative]
    abel
  have hRow (k c b : I) : metricDensity d.γ y*((d.γ y)⁻¹ k c*(
      ⟪Z (RA c (H b)),Z (BA b (H k))⟫_ℝ-⟪Z (RA c (H k)),Z (BA b (H b))⟫_ℝ))-
      balancedHalfHodgePairDensity d (modelFirstLeadingWeight d k c)
        (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b)
        (modelFirstRaisingAdjointSourceHigher d U c) (P.firstCovariantAdjointFiveHalfSection W U b)
        (axis k) (axis b) y=
      modelFirstLeadingWeight d k c y*modelFirstExchangeJetCorrection (RA c) (BA b) (H k) (H b) (r c k) (r c b) (s b k) (s b b) := by
    have hRk := hDR c k
    have hRb := hDR c b
    change balancedPositiveHalfDerivative d (modelFirstRaisingAdjointSource d U c)
      (modelFirstRaisingAdjointSourceHigher d U c) y (axis k)=RA c (H k)+r c k at hRk
    change balancedPositiveHalfDerivative d (modelFirstRaisingAdjointSource d U c)
      (modelFirstRaisingAdjointSourceHigher d U c) y (axis b)=RA c (H b)+r c b at hRb
    have hExp := model_first_hodge_row_expansion (RA c) (BA b) (H k) (H b) (r c k) (r c b) (s b k) (s b b)
    unfold balancedHalfHodgePairDensity
    rw [hRk,hRb]
    change metricDensity d.γ y*((d.γ y)⁻¹ k c*(_-_))-
      modelFirstLeadingWeight d k c y*(⟪Z (RA c (H b)+r c b),Z (firstSelfAdjointSourceDerivative P WF W U b k y)⟫_ℝ-
        ⟪Z (RA c (H k)+r c k),Z (firstSelfAdjointSourceDerivative P WF W U b b y)⟫_ℝ)=_
    rw [hDB b k,hDB b b]
    exact model_first_hodge_scale (metricDensity d.γ y) ((d.γ y)⁻¹ k c) _ _ _ hExp
  unfold modelFirstJetDensity modelFirstCrossedDensity modelFirstHodgeDensity
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_congr rfl (fun b _ => hRow k c b)

/-- Every jet product is estimated through the true LOW transpose and
original half horizontal derivative, never an uncontrolled H3/2 derivative. -/
theorem model_first_actual_jet_point_bound
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor R0 R1 B0 B1 CA CL : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hε : 0 ≤ ε)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y)
    (hR : ∀ c,‖framedRaisingHalfL d y (axis c)‖ ≤ R0)
    (hRJ : ∀ c i,‖modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c i y‖ ≤ R1)
    (hB : ∀ b,‖P.firstCovariantCoordinateHalfL b y‖ ≤ B0*ε/beta d.γ d.radius y)
    (hPoint : FirstSelfAdjointSourcePointBounds P WF W U y CA CL B1) :
    |modelFirstJetDensity P WF W U y| ≤ (27*K*(4*R0*B1+4*B0*R1+2*R1*B1))*ε*metricDensity d.γ y*
      ∑ i : I,halfCovariantDirectionEnergy d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i) := by
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let β := beta d.γ d.radius y
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  let C := 4*R0*B1+4*B0*R1+2*R1*B1
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hEnergy := model_first_component_energy_controls d U3 y β hβ
  have hGrad (i : I) : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (fiveHalfCovariantDerivative d U (axis i) y)‖^2 ≤ En := by
    rw [fiveHalfCovariantDerivative_half_inclusion d U y (axis i) ((hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]
    exact hEnergy.2 i
  rw [modelFirstJetDensity_eq_rows hY hΩ hd (zero_lt_one.trans_le hK) P WF W U hU hy]
  have hEach (k c b : I) : |modelFirstLeadingWeight d k c y*modelFirstExchangeJetCorrection
      (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y) (WF.covariantCoordinateAdjointHigher b y)
      (fiveHalfCovariantDerivative d U (axis k) y) (fiveHalfCovariantDerivative d U (axis b) y)
      (modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c k y (U3 y))
      (modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c b y (U3 y))
      (firstSelfAdjointSourceJetError P WF W U b k y) (firstSelfAdjointSourceJetError P WF W U b b y)| ≤
      K*metricDensity d.γ y*(C*ε*En) := by
    have hQ : |modelFirstLeadingWeight d k c y| ≤ K*metricDensity d.γ y := by
      rw [modelFirstLeadingWeight,abs_mul,abs_of_nonneg (show 0 ≤ metricDensity d.γ y from Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hd.1.1.inverse_entry_bound (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy) k c)
        (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _)
    have hCorr := model_first_hodge_jet_correction_bound (framedRaisingHalfL d y (axis c)) (P.firstCovariantCoordinateHalfL b y)
      (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y) (WF.covariantCoordinateAdjointHigher b y)
      (scalarModelRaisingAdjointHigher_balanced modelFirstFlatAdjointHigher d c y modelFirstFlatAdjointHigher_graph)
      (WF.covariantCoordinateAdjointHigher_balanced b hy) _ _ _ _ _ _ R0 R1 B0 B1 ε β ‖U3 y‖ En
      hR0 hR1 hB0 hB1 hε hβ (norm_nonneg _) (hR c) (hB b)
      (((modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c k y).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hRJ c k) (norm_nonneg _)))
      (((modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c b y).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hRJ c b) (norm_nonneg _)))
      (hPoint.error b k) (hPoint.error b b) hEnergy.1 (hGrad k) (hGrad b)
    rw [abs_mul]
    exact mul_le_mul hQ hCorr (abs_nonneg _) (mul_nonneg (zero_le_one.trans hK) (Real.sqrt_nonneg _))
  have hSum := abs_fin_three_sum_le _ _ (fun k => abs_fin_three_sum_le _ _ (fun c => abs_fin_three_sum_le _ _ (hEach k c)))
  exact hSum.trans_eq (by dsimp only [C,En,U3,β];ring)

end ShrinkingSpheres.ParallelEnergy
