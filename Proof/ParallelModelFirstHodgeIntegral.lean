import Proof.ParallelModelFirstRaisingBudget
import Proof.ParallelFirstSelfHodgeIntegral
import Proof.EffectiveFirstAdjointCoreSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_first_finite_green_family {ι : Type*} [Fintype ι] (Y : Set X)
    (f g : ι → X → ℝ)
    (h : ∀ i,IntegrableOn (f i) Y ∧ IntegrableOn (g i) Y ∧ (∫ x in Y,f i x)=∫ x in Y,g i x) :
    IntegrableOn (fun x => ∑ i,f i x) Y ∧ IntegrableOn (fun x => ∑ i,g i x) Y ∧
      (∫ x in Y,∑ i,f i x)=∫ x in Y,∑ i,g i x := by
  refine ⟨integrable_finsetSum _ (fun i _ => (h i).1),integrable_finsetSum _ (fun i _ => (h i).2.1),?_⟩
  rw [integral_finsetSum _ (fun i _ => (h i).1),integral_finsetSum _ (fun i _ => (h i).2.1)]
  exact Finset.sum_congr rfl (fun i _ => (h i).2.2)

def modelFirstRaisingAdjointSource (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (c : I) (y : X) :
    SphereSobolev (1/2:ℝ) :=
  scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))

def modelFirstLeadingWeight (d : Data) (k c : I) (y : X) : ℝ := metricDensity d.γ y*(d.γ y)⁻¹ k c

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def modelFirstHodgeDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ k : I,∑ c : I,∑ b : I,balancedHalfHodgePairDensity d (modelFirstLeadingWeight d k c)
    (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b)
    (modelFirstRaisingAdjointSourceHigher d U c) (P.firstCovariantAdjointFiveHalfSection W U b)
    (axis k) (axis b) y

def modelFirstHodgeRemainder {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ k : I,∑ c : I,∑ b : I,balancedHalfHodgePairRemainder d (modelFirstLeadingWeight d k c)
    (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b) (axis k) (axis b) y

/-- The actual mixed model/first Hodge exchange is integrable and has
exactly the curvature/density remainder. The arbitrary physical WF/W
are retained and neither pointwise higher lift is differentiated. -/
theorem model_first_actual_hodge_integral
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelFirstHodgeDensity P WF W U) Y ∧
      IntegrableOn (modelFirstHodgeRemainder WF U) Y ∧
      (∫ y in Y,modelFirstHodgeDensity P WF W U y)=∫ y in Y,modelFirstHodgeRemainder WF U y := by
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  have hU3 : ContDiff ℝ ∞ U3 := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
  have hU30 (x : X) (hx : x ∉ S) : U3 x=0 := by simp only [U3,hU0 x hx,map_zero]
  have hRS (c : I) : ContDiff ℝ ∞ (modelFirstRaisingAdjointSource d U c) :=
    OperatorForms.contDiff_supported_operator_apply U3 (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c)
      S hS.isClosed hU3 hU30 (fun x hx => (scalarModelRaisingAdjointHigher_smooth hd modelFirstFlatAdjointHigher c).contDiffAt
        (hY.mem_nhds (hSY hx)))
  have hR0 (c : I) (x : X) (hx : x ∉ S) : modelFirstRaisingAdjointSource d U c x=0 := by
    simp only [modelFirstRaisingAdjointSource,hU0 x hx,map_zero]
  have hBS (b : I) := WF.covariantAdjointLowSection_supported hY hd U hU S hS.isClosed hSY hU0 b
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b)
  have hq (k c : I) : ContDiffOn ℝ ∞ (modelFirstLeadingWeight d k c) Y :=
    (hg.contDiffOn_density hK).mul (hg.contDiffOn_inverse_entry hK k c)
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  let F := fun k c b => balancedHalfHodgePairDensity d (modelFirstLeadingWeight d k c)
    (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b)
    (modelFirstRaisingAdjointSourceHigher d U c) (P.firstCovariantAdjointFiveHalfSection W U b) (axis k) (axis b)
  let R := fun k c b => balancedHalfHodgePairRemainder d (modelFirstLeadingWeight d k c)
    (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b) (axis k) (axis b)
  have hEach (k c b : I) : IntegrableOn (F k c b) Y ∧ IntegrableOn (R k c b) Y ∧
      (∫ y in Y,F k c b y)=∫ y in Y,R k c b y :=
    balanced_half_hodge_pair_integral hY d hg hK he hFrame _ (hq k c) _ _ _ _ (hRS c) (hBS b).1
      S hS hSY (hR0 c) (hBS b).2
      (fun x _ => modelFirstRaisingAdjointSourceHigher_graph Q hQ modelFirstFlatAdjointHigher
        modelFirstFlatAdjointHigher_graph d U c x)
      (fun x hx => firstSelfAdjointSource_higher_graph P WF W U b hx) (axis k) (axis b)
  exact model_first_finite_green_family Y _ _ (fun k =>
    model_first_finite_green_family Y _ _ (fun c => model_first_finite_green_family Y _ _ (hEach k c)))

end ShrinkingSpheres.ParallelEnergy
