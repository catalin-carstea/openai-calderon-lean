import Proof.ParallelModelFirstLeadingPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact integrated leading comparison for distinct model/complete-first
coefficients. Every actual integral is established before the Hodge exchange;
no chosen high source is assigned unproved measurability or smoothness. -/
theorem model_first_leading_integral_reduction
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hP : ∀ b y,y ∈ Y →
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
        (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    IntegrableOn (modelFirstLeadingDensity P WF U) Y ∧
      IntegrableOn (fun y => modelFirstAngularCommutatorDensity P WF U y+
        modelFirstHodgeRemainder WF U y+modelFirstJetDensity P WF W U y) Y ∧
      (∫ y in Y,modelFirstLeadingDensity P WF U y)=
        ∫ y in Y,modelFirstAngularCommutatorDensity P WF U y+modelFirstHodgeRemainder WF U y+modelFirstJetDensity P WF W U y := by
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  let H := fun i : I => fiveHalfCovariantDerivative d U (axis i)
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let RH := fun c x => framedRaisingHigherL d x (axis c)
  let RA := scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d
  let BA := WF.covariantCoordinateAdjointHigher
  have hH (i : I) : ContDiff ℝ ∞ (H i) ∧ ∀ x ∉ S,H i x=0 :=
    contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU S hS.isClosed hSY h0U (axis i)
  have hApp (A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      (hA : ContDiffOn ℝ ∞ A Y) (i : I) :
      ContDiff ℝ ∞ (fun x => Z (A x (H i x))) ∧ ∀ x ∉ S,Z (A x (H i x))=0 := by
    refine ⟨Z.contDiff.comp (OperatorForms.contDiff_supported_operator_apply (H i) A S hS.isClosed (hH i).1 (hH i).2
      (fun x hx => hA.contDiffAt (hY.mem_nhds (hSY hx)))),?_⟩
    intro x hx
    rw [(hH i).2 x hx,map_zero,map_zero]
  have hMem (A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      (hA : ContDiffOn ℝ ∞ A Y) (i : I) : MemLp (fun x => Z (A x (H i x))) 2 (volume.restrict Y) :=
    (hApp A hA i).1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS (hApp A hA i).2)
  have hRS (c : I) : ContDiffOn ℝ ∞ (RH c) Y := (hd.framedRaisingHalf_smooth (axis c)).2.1
  have hAS (c : I) : ContDiffOn ℝ ∞ (RA c) Y := scalarModelRaisingAdjointHigher_smooth hd modelFirstFlatAdjointHigher c
  have hBS (b : I) : ContDiffOn ℝ ∞ (BA b) Y := WF.covariantCoordinateAdjointHigher_smooth hd b
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b)
  have hq (k c : I) : ContDiffOn ℝ ∞ (modelFirstLeadingWeight d k c) Y :=
    (hg.contDiffOn_density hK).mul (hg.contDiffOn_inverse_entry hK k c)
  let U2 := fiveHalfToTwoSection U
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h02 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,h0U x hx,map_zero]
  have hFLp (b : I) := P.firstCovariantCoreRow_memLp hY hΩ hSub hd hK U2 hU2 S hS hSY h02 b
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b) 2
  let F := fun k c b x => modelFirstLeadingWeight d k c x*⟪Z (RH c x (H k x)),P.firstCovariantCoreRow U2 b x⟫_ℝ
  let A := fun k c b x => modelFirstLeadingWeight d k c x*⟪Z (RA c x (H k x)),Z (BA b x (H b x))⟫_ℝ
  let Xc := fun k c b x => modelFirstLeadingWeight d k c x*⟪Z (RA c x (H b x)),Z (BA b x (H k x))⟫_ℝ
  have hFI (k c b : I) : IntegrableOn (F k c b) Y :=
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ (hMem (RH c) (hRS c) k) (hFLp b)
      (fun x _ hx => (hApp (RH c) (hRS c) k).2 x hx) _ (hq k c).continuousOn
  have hAI (k c b : I) : IntegrableOn (A k c b) Y :=
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ (hMem (RA c) (hAS c) k) (hMem (BA b) (hBS b) b)
      (fun x _ hx => (hApp (RA c) (hAS c) k).2 x hx) _ (hq k c).continuousOn
  have hXI (k c b : I) : IntegrableOn (Xc k c b) Y :=
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ (hMem (RA c) (hAS c) b) (hMem (BA b) (hBS b) k)
      (fun x _ hx => (hApp (RA c) (hAS c) b).2 x hx) _ (hq k c).continuousOn
  have hIF : IntegrableOn (fun x => ∑ k : I,∑ c : I,∑ b : I,(F k c b x-A k c b x)) Y :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun b _ => (hFI k c b).sub (hAI k c b))))
  have hIX : IntegrableOn (fun x => ∑ k : I,∑ c : I,∑ b : I,(Xc k c b x-A k c b x)) Y :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun b _ => (hXI k c b).sub (hAI k c b))))
  have hEqF : modelFirstLeadingDensity P WF U=ᵐ[volume.restrict Y]
      fun x => ∑ k : I,∑ c : I,∑ b : I,(F k c b x-A k c b x) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hRow (b : I) : Z (P.firstCovariantCoordinateHigherL b x (H b x))=P.firstCovariantCoreRow U2 b x := by
      have hh := model_first_coarse_high_pair_of_graph (P.firstCovariantCoordinateCoarseL b x)
        (P.firstCovariantCoordinateHalfL b x) (P.firstCovariantCoordinateHigherL b x)
        (P.firstCovariantCoordinate_coarse_half_compatible hd hY hx b) (hP b x hx) (H b x)
      rw [fiveHalfCovariantDerivative_inclusion d U x (axis b) (hU.differentiable (by simp) x)] at hh
      exact hh
    simp only [modelFirstLeadingDensity,F,A,RH,RA,BA,H,Z,Finset.mul_sum,mul_sub,mul_assoc,modelFirstLeadingWeight,←hRow]
  have hEqX : modelFirstCrossedDensity P WF U=fun x => ∑ k : I,∑ c : I,∑ b : I,(Xc k c b x-A k c b x) := by
    funext x
    simp only [modelFirstCrossedDensity,Xc,A,RA,BA,H,Z,Finset.mul_sum,mul_sub,mul_assoc,modelFirstLeadingWeight]
  have hLI : IntegrableOn (modelFirstLeadingDensity P WF U) Y := hIF.congr hEqF.symm
  have hXI' : IntegrableOn (modelFirstCrossedDensity P WF U) Y := by rw [hEqX];exact hIX
  have hCI : IntegrableOn (modelFirstAngularCommutatorDensity P WF U) Y := by
    apply (hLI.sub hXI').congr
    exact Eventually.of_forall (fun x => by
      have hh := modelFirstLeadingDensity_hodge_split P WF W U x
      dsimp only [modelFirstJetDensity] at hh
      change modelFirstLeadingDensity P WF U x-modelFirstCrossedDensity P WF U x=_
      linarith only [hh])
  have hGreen := model_first_actual_hodge_integral hY hSub hd hK P WF W U hU S hS hSY h0U
  have hJI : IntegrableOn (modelFirstJetDensity P WF W U) Y := hXI'.sub hGreen.1
  have hRI : IntegrableOn (fun x => modelFirstAngularCommutatorDensity P WF U x+modelFirstHodgeRemainder WF U x+modelFirstJetDensity P WF W U x) Y :=
    (hCI.add hGreen.2.1).add hJI
  refine ⟨hLI,hRI,?_⟩
  have hId : modelFirstLeadingDensity P WF U=fun x => modelFirstAngularCommutatorDensity P WF U x+
      modelFirstHodgeDensity P WF W U x+modelFirstJetDensity P WF W U x := funext (modelFirstLeadingDensity_hodge_split P WF W U)
  have hCH : IntegrableOn (fun x => modelFirstAngularCommutatorDensity P WF U x+modelFirstHodgeDensity P WF W U x) Y := hCI.add hGreen.1
  have hCR : IntegrableOn (fun x => modelFirstAngularCommutatorDensity P WF U x+modelFirstHodgeRemainder WF U x) Y := hCI.add hGreen.2.1
  calc
    _ = ∫ x in Y,modelFirstAngularCommutatorDensity P WF U x+modelFirstHodgeDensity P WF W U x+modelFirstJetDensity P WF W U x :=
      integral_congr_ae (Eventually.of_forall (fun x => congrFun hId x))
    _ = (∫ x in Y,modelFirstAngularCommutatorDensity P WF U x)+(∫ x in Y,modelFirstHodgeDensity P WF W U x)+
        (∫ x in Y,modelFirstJetDensity P WF W U x) := by rw [integral_add hCH hJI,integral_add hCI hGreen.1]
    _ = (∫ x in Y,modelFirstAngularCommutatorDensity P WF U x)+(∫ x in Y,modelFirstHodgeRemainder WF U x)+
        (∫ x in Y,modelFirstJetDensity P WF W U x) := by rw [hGreen.2.2]
    _ = _ := by rw [integral_add hCR hJI,integral_add hCI hGreen.2.1]

end ShrinkingSpheres.ParallelEnergy
