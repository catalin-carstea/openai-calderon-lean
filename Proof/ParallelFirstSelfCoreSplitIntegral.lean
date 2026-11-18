import Proof.ParallelFirstSelfCoreSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

lemma firstAdjointLeadingCoreRow_supported
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I) :
    ContDiff ℝ ∞ (firstAdjointLeadingCoreRow WF U b) ∧
      ∀ x ∉ S,firstAdjointLeadingCoreRow WF U b x=0 := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hDU := contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU
    S hS hSY h0U (axis b)
  have hC := WF.covariantCoordinateAdjointHigher_smooth hd b
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b)
  have hApply := contDiff_supported_operator_apply _ _ S hS hDU.1 hDU.2
    (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
  refine ⟨((sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).contDiff.comp hApply).neg,?_⟩
  intro x hx
  simp only [firstAdjointLeadingCoreRow,firstSelfSourceDerivative,hDU.2 x hx,map_zero,neg_zero]

lemma firstAdjointLeadingCoreSection_memLp
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (p : ℝ≥0∞) :
    MemLp (firstAdjointLeadingCoreSection WF U) p (volume.restrict Y) := by
  apply memLp_finsetSum Finset.univ
  intro b _
  have hOut := firstAdjointLeadingCoreRow_supported hY hSub hd hK WF U hU S hS.isClosed hSY h0U b
  exact hOut.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hOut.2)

/-- Each split term is genuinely integrable; no cancellation is used to
mask a missing L2 domain. -/
theorem firstSelf_core_split_integrableOn
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (fun y => metricDensity d.γ y*(
      ‖P.firstCovariantCoreSection (fiveHalfToTwoSection U) y‖^2-
      ‖firstAdjointLeadingCoreSection WF U y‖^2)) Y ∧
    IntegrableOn (fun y => 2*metricDensity d.γ y*
      ⟪firstAdjointLeadingCoreSection WF U y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*‖firstAdjointDefectCoreSection P WF W U y‖^2) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hL := firstAdjointLeadingCoreSection_memLp hY hSub hd hK WF U hU S hS hSY h0U 2
  have hA := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw 2
  have hD : MemLp (firstAdjointDefectCoreSection P WF W U) 2 (volume.restrict Y) := hA.sub hL
  have h0L (y : X) (hy : y ∉ S) : firstAdjointLeadingCoreSection WF U y=0 := by
    unfold firstAdjointLeadingCoreSection
    exact Finset.sum_eq_zero (fun b _ =>
      (firstAdjointLeadingCoreRow_supported hY hSub hd hK WF U hU S hS.isClosed hSY h0U b).2 y hy)
  have h0D (y : X) (hy : y ∉ S) : firstAdjointDefectCoreSection P WF W U y=0 := by
    unfold firstAdjointDefectCoreSection
    rw [P.firstFormalAdjointCore_zero_off hY hd WF W U hU S hS.isClosed hSY h0U hw hy,h0L y hy,sub_self]
  have hμ := (hg.contDiffOn_density hK).continuousOn
  have hμ0 (y : X) (_hy : y ∈ Y) : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hLI := integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hL
    (fun y _ hy => h0L y hy) _ hμ hμ0
  have hDI := integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hD
    (fun y _ hy => h0D y hy) _ hμ hμ0
  have hCross := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hL hD
    (fun y _ hy => h0L y hy) _ hμ
  have hV : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h0V (x) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by
    simp only [fiveHalfToTwoSection,h0U x hx,map_zero]
  have hF := (P.firstCoreOperators_weighted_square_integrable hY hΩ hSub hd hK WF W hCG hCK
    U (fiveHalfToTwoSection U) hU hV S hS hSY h0U h0V hw).1
  refine ⟨?_,?_,hDI⟩
  · simp_rw [mul_sub]
    exact hF.sub hLI
  · change Integrable _ (volume.restrict Y)
    simpa only [mul_assoc] using hCross.const_mul 2

end ShrinkingSpheres.ParallelEnergy
