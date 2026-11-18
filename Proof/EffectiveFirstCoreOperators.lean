import Proof.EffectiveFirstFormalAdjointCore
import Proof.CompactSupportedLpWeightedSquare
import Proof.PhysicalFirstCoordinateCoarse
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms
namespace PhysicalPrincipalData
variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

def firstCovariantCoreRow (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) (b : I) (y : X) : SphereSobolev 0 :=
  P.firstCovariantCoordinateCoarseL b y (highSectionCovariantDerivative d U y (axis b))

def firstCovariantCoreSection (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 := ∑ b : I,P.firstCovariantCoreRow U b y

def firstFormalAdjointCore (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev 0 :=
  ∑ b : I,P.firstFormalAdjointCoreRow WF WQ U b y

lemma firstCovariantCoreRow_supported (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContDiff ℝ ∞ (P.firstCovariantCoreRow U b) ∧ ∀ x ∉ S,P.firstCovariantCoreRow U b x=0 := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hD := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU S hS hSY h0U (axis b)
  have hB : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y :=
    (P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub hK b).sub (hw.smul contDiffOn_const)
  refine ⟨contDiff_supported_operator_apply _ _ S hS hD.1 hD.2
    (fun x hx => hB.contDiffAt (hY.mem_nhds (hSY hx))),?_⟩
  intro x hx
  simp only [firstCovariantCoreRow,hD.2 x hx,map_zero]

lemma firstCovariantCoreRow_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstCovariantCoreRow U b) p (volume.restrict Y) := by
  have hOut := P.firstCovariantCoreRow_supported hY hΩ hSub hd hK U hU S hS.isClosed hSY h0U b hw
  exact hOut.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hOut.2)

lemma firstCovariantCoreSection_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstCovariantCoreSection U) p (volume.restrict Y) :=
  memLp_finsetSum Finset.univ (fun b _ => P.firstCovariantCoreRow_memLp hY hΩ hSub hd hK U hU S hS hSY h0U b (hw b) p)

lemma firstFormalAdjointCoreRow_zero_off (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∉ S) :
    P.firstFormalAdjointCoreRow WF WQ U b y=0 := by
  simp only [firstFormalAdjointCoreRow,
    P.firstAdjointDensityCoreRow_zero_off hY hd WF WQ U hU S hS hSY h0U b hw hy,map_zero,smul_zero]

lemma firstFormalAdjointCore_zero_off (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∉ S) :
    P.firstFormalAdjointCore WF WQ U y=0 :=
  Finset.sum_eq_zero (fun b _ => P.firstFormalAdjointCoreRow_zero_off hY hd WF WQ U hU S hS hSY h0U b (hw b) hy)

lemma firstFormalAdjointCore_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstFormalAdjointCore WF WQ U) p (volume.restrict Y) :=
  memLp_finsetSum Finset.univ (fun b _ => P.firstFormalAdjointCoreRow_memLp hY hΩ hSub hd hK WF WQ hCG hCK U hU S hS hSY h0U b (hw b) p)

theorem firstCoreOperators_weighted_square_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (V : X → SphereSobolev 2)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    IntegrableOn (fun y => metricDensity d.γ y*‖P.firstCovariantCoreSection V y‖^2) Y ∧
      IntegrableOn (fun y => metricDensity d.γ y*‖P.firstFormalAdjointCore WF WQ U y‖^2) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have h0F (y) (hy : y ∉ S) : P.firstCovariantCoreSection V y=0 :=
    Finset.sum_eq_zero (fun b _ => (P.firstCovariantCoreRow_supported hY hΩ hSub hd hK V hV S hS.isClosed hSY h0V b (hw b)).2 y hy)
  refine ⟨integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _
    (P.firstCovariantCoreSection_memLp hY hΩ hSub hd hK V hV S hS hSY h0V hw 2)
    (fun y _ hy => h0F y hy) _ (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _),
    integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _
      (P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF WQ hCG hCK U hU S hS hSY h0U hw 2)
      (fun _ _ hy => P.firstFormalAdjointCore_zero_off hY hd WF WQ U hU S hS.isClosed hSY h0U hw hy) _
      (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _)⟩

end PhysicalPrincipalData
end ShrinkingSpheres
