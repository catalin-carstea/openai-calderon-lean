import Proof.ParallelFirstSelfHodgeIntegral
import Proof.ParallelFirstSelfAdjointSourceProduct
import Proof.EffectiveFirstAdjointCoreSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfAdjointSourceHodgeDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ b : I,∑ c : I,balancedHalfHodgePairDensity d (metricDensity d.γ)
    (WF.covariantAdjointLowSection U b) (WF.covariantAdjointLowSection U c)
    (P.firstCovariantAdjointFiveHalfSection W U b) (P.firstCovariantAdjointFiveHalfSection W U c)
    (axis b) (axis c) y

def firstSelfAdjointSourceHodgeRemainder {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ b : I,∑ c : I,balancedHalfHodgePairRemainder d (metricDensity d.γ)
    (WF.covariantAdjointLowSection U b) (WF.covariantAdjointLowSection U c) (axis b) (axis c) y

/-- Actual Hodge exchange for the SAME P/WF/W. Only its complete crossed
contraction is asserted integrable, without separate HIGH measurability. -/
theorem first_self_actual_adjoint_hodge_integral
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (firstSelfAdjointSourceHodgeDensity P WF W U) Y ∧
      IntegrableOn (firstSelfAdjointSourceHodgeRemainder WF U) Y ∧
      (∫ y in Y,firstSelfAdjointSourceHodgeDensity P WF W U y)=
        ∫ y in Y,firstSelfAdjointSourceHodgeRemainder WF U y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hw (b : I) := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b
  have hSource (b : I) := WF.covariantAdjointLowSection_supported hY hd U hU S hS.isClosed hSY hU0 b (hw b)
  let L := fun b => WF.covariantAdjointLowSection U b
  let H := fun b => P.firstCovariantAdjointFiveHalfSection W U b
  let F := fun b c => balancedHalfHodgePairDensity d (metricDensity d.γ) (L b) (L c) (H b) (H c) (axis b) (axis c)
  let R := fun b c => balancedHalfHodgePairRemainder d (metricDensity d.γ) (L b) (L c) (axis b) (axis c)
  have hEach (b c : I) : IntegrableOn (F b c) Y ∧ IntegrableOn (R b c) Y ∧
      (∫ y in Y,F b c y)=∫ y in Y,R b c y :=
    balanced_half_hodge_pair_integral hY d hg hK he hFrame (metricDensity d.γ) (hg.contDiffOn_density hK)
      (L b) (L c) (H b) (H c) (hSource b).1 (hSource c).1 S hS hSY (hSource b).2 (hSource c).2
      (fun y hy => firstSelfAdjointSource_higher_graph P WF W U b hy)
      (fun y hy => firstSelfAdjointSource_higher_graph P WF W U c hy) (axis b) (axis c)
  have hFI (b : I) : IntegrableOn (fun y => ∑ c : I,F b c y) Y :=
    integrable_finset_sum _ (fun c _ => (hEach b c).1)
  have hRI (b : I) : IntegrableOn (fun y => ∑ c : I,R b c y) Y :=
    integrable_finset_sum _ (fun c _ => (hEach b c).2.1)
  refine ⟨integrable_finset_sum _ (fun b _ => hFI b),integrable_finset_sum _ (fun b _ => hRI b),?_⟩
  change (∫ y in Y,∑ b : I,∑ c : I,F b c y)=∫ y in Y,∑ b : I,∑ c : I,R b c y
  rw [integral_finset_sum _ (fun b _ => hFI b),integral_finset_sum _ (fun b _ => hRI b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finset_sum _ (fun c _ => (hEach b c).1),integral_finset_sum _ (fun c _ => (hEach b c).2.1)]
  exact Finset.sum_congr rfl (fun c _ => (hEach b c).2.2)

end ShrinkingSpheres.ParallelEnergy
