module

public import Proof.CalderonN.ActualTraceRaisingSymbol
public import Proof.CalderonN.CoordinateTraceFirstOrderAdjoint
public import Proof.CalderonN.TraceCoordinatePotential

public import Proof.CalderonN.PhysicalTraceModelAdjoint
import Mathlib.Tactic

/-! The angular model, leading velocity, and horizontal potential
are built from one shared coordinate frame and the same degree
and rotation operators. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4750000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

structure CoordinateTraceModelFactors (hn : 3 ≤ dim) (Y : Set (X dim)) where
  degree : PairedTraceFiberFamily hn Y
  rotation : I dim → I dim → PairedTraceFiberFamily hn Y
  raising : I dim → PairedTraceFiberFamily hn Y
  frameEntry : I dim → I dim → PairedTraceFiberFamily hn Y
  coframeEntry : I dim → I dim → PairedTraceFiberFamily hn Y
  connection : I dim → I dim → I dim → PairedTraceFiberFamily hn Y
  logGradient : I dim → PairedTraceFiberFamily hn Y
  connectionDerivative : I dim → I dim → I dim → I dim → PairedTraceFiberFamily hn Y
  logGradientDerivative : I dim → I dim → PairedTraceFiberFamily hn Y

namespace CoordinateTraceModelFactors

@[expose] def potential (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  (PairedTraceFiberFamily.finiteSum Finset.univ (fun a =>
    PairedTraceFiberFamily.finiteSum Finset.univ (fun b => (F.connection i a b).mul hY (F.rotation a b)))).add
      ((F.logGradient i).mul hY F.degree)

@[expose] def potentialDerivative (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) (i j : I dim) :
    PairedTraceFiberFamily hn Y :=
  (PairedTraceFiberFamily.finiteSum Finset.univ (fun a =>
    PairedTraceFiberFamily.finiteSum Finset.univ (fun b => (F.connectionDerivative i j a b).mul hY (F.rotation a b)))).add
      ((F.logGradientDerivative i j).mul hY F.degree)

@[expose] def leading (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun a => (F.coframeEntry a i).mul hY (F.raising a))

@[expose] def first (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun a => (F.frameEntry a i).mul hY (F.raising a))

@[expose] def zero (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) :
    PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun i => (F.first hY i).mul hY (F.potential hY i))

@[expose] def correction (hY : IsOpen Y) (F : CoordinateTraceModelFactors hn Y) :
    PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun i => (F.logGradient i).mul hY (F.first hY i).adj)

end CoordinateTraceModelFactors

section Actual
variable (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  (hg : Elliptic Y K g) (hK : 0 < K) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  {r : X dim → ℝ} (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)
  {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

@[expose] def actualCoordinateTraceModelFactors : CoordinateTraceModelFactors hn Y where
  degree := PairedTraceFiberFamily.degree hA hEll S
  rotation := PairedTraceFiberFamily.rotation
  raising := PairedTraceFiberFamily.raising hA hEll S hY
  frameEntry := fun a i => PairedTraceFiberFamily.scalar hY (fun x => e x a i)
    (contDiffOn_vector_component _ (he a) i)
  coframeEntry := fun a i => PairedTraceFiberFamily.scalar hY (traceFrameCoordinate g e a i)
    (contDiffOn_traceFrameCoordinate hg he a i)
  connection := fun i a b => PairedTraceFiberFamily.scalar hY (traceCoordinateConnectionScalar g e i a b)
    (contDiffOn_traceCoordinateConnectionScalar hY hg hK he i a b)
  logGradient := fun i => PairedTraceFiberFamily.scalar hY (traceCoordinateLogGradient r i)
    (contDiffOn_traceCoordinateLogGradient hY hlog i)

  connectionDerivative := fun i j a b => PairedTraceFiberFamily.scalar hY
    (coordDeriv i (traceCoordinateConnectionScalar g e j a b))
    (((contDiffOn_traceCoordinateConnectionScalar hY hg hK he j a b).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply
      contDiffOn_const)
  logGradientDerivative := fun i j => PairedTraceFiberFamily.scalar hY
    (coordDeriv i (traceCoordinateLogGradient r j))
    (((contDiffOn_traceCoordinateLogGradient hY hlog j).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const)

set_option linter.unusedSectionVars false in
theorem actualCoordinateTraceModel_potential (i : I dim) :
    let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
    (F.potential hY i).forward.action hY = supportedCoordinateModelPotential hY hg hK he hA hEll S hlog i := by
  simp only [actualCoordinateTraceModelFactors,CoordinateTraceModelFactors.potential,PairedTraceFiberFamily.add,
    PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,
    RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_finiteSum,
    RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_scalar,supportedCoordinateModelPotential]
  rfl

theorem actualCoordinateTraceModel_leading (i : I dim) :
    let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
    (F.leading hY i).forward.action hY = supportedCoordinateRaising hY hg he hA hEll S i := by
  simp only [actualCoordinateTraceModelFactors,CoordinateTraceModelFactors.leading,
    PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,
    RegularTraceFiberFamily.action_finiteSum,RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_scalar,
    supportedCoordinateRaising]
  rfl

theorem actualCoordinateTraceModel_potentialDerivative (i j : I dim) :
    let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
    (F.potentialDerivative hY i j).forward.action hY =
      supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog i j := by
  simp only [actualCoordinateTraceModelFactors,CoordinateTraceModelFactors.potentialDerivative,PairedTraceFiberFamily.add,
    PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,
    RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_finiteSum,
    RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_scalar,supportedCoordinateModelPotentialDerivative]
  rfl

theorem actualCoordinateTraceModel_firstOrder
    (hFrame : ∀ x ∈ Y,∀ a b,metricPair g x (e x a) (e x b) = if a=b then 1 else 0) :
    let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
    (CoordinateTraceFirstOrder.ofPaired (F.first hY) (F.zero hY)).action hY =
      physicalRaisingModel hY hg hK he hlog hA hEll S := by
  dsimp only
  let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let P (i : I dim) := (F.first hY i).forward.action hY
  let K₀ (i : I dim) := (F.potential hY i).forward.action hY
  let L (i : I dim) := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i
  let R (a : I dim) := supportedRaising hA hEll S hY a
  let M (a i : I dim) := smoothSupportedTraceBaseMul hY (fun x => e x a i) (contDiffOn_vector_component _ (he a) i)
  have hK' (i : I dim) : L i = D i+K₀ i := by
    change L i = D i+(F.potential hY i).forward.action hY
    rw [actualCoordinateTraceModel_potential]
    exact supportedCoordinateModelDerivative_eq_base_add_potential hY hg hK he hA hEll S hlog i
  have hP (i : I dim) : P i = ∑ a : I dim,M a i*R a := by
    simp only [P,F,CoordinateTraceModelFactors.first,actualCoordinateTraceModelFactors,
      PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,
      RegularTraceFiberFamily.action_finiteSum,RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_scalar]
    rfl
  have hSum : (F.zero hY).forward.action hY = ∑ i,P i*K₀ i := by
    simp only [CoordinateTraceModelFactors.zero,PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,
      RegularTraceFiberFamily.action_finiteSum,RegularTraceFiberFamily.action_mul,P,K₀]
  change (∑ i,P i*D i)+(F.zero hY).forward.action hY = _
  rw [hSum,← Finset.sum_add_distrib]
  simp_rw [← mul_add,← hK']
  change (∑ i,P i*L i) = ∑ a,R a*(supportedHorizontal hY hg hK he (fun x => e x a) (he a)+
    smoothSupportedTraceBaseMul hY (traceModelLogGradient e r a) (contDiffOn_traceModelLogGradient hY he hlog a)*
      supportedFlatDegree hA hEll S hY)
  simp_rw [supportedFrameModelDerivative_eq_sum hY hg hK he hlog hA hEll S hFrame,hP,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  have hM : M a i*R a = R a*M a i := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x _
    simp only [R,M,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberAction_fiber,map_smul]
  rw [← mul_assoc,hM]

theorem actualCoordinateTraceModel_correction :
    let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
    (F.correction hY).forward.action hY = physicalTraceModelCorrection hY he hA hEll S hlog := by
  dsimp only
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  let v := smoothSupportedTraceFiberL x u
  let f (i : I dim) := traceCoordinateLogGradient r i x
  let L (a : I dim) := smoothTraceLowering (smoothTraceFlatDegree hA hEll S) a
  simp only [RegularTraceFiberFamily.action_fiber,CoordinateTraceModelFactors.correction,CoordinateTraceModelFactors.first,
    actualCoordinateTraceModelFactors,PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.adj,
    PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,PairedTraceFiberFamily.raising,
    RegularTraceFiberFamily.finiteSum,RegularTraceFiberFamily.scalar,RegularTraceFiberFamily.mul,
    LinearMap.sum_apply,Module.End.mul_apply,LinearMap.smul_apply,Module.End.one_apply,map_smul,Finset.smul_sum,smul_smul,
    physicalTraceModelCorrection,smoothSupportedTraceBaseMul_fiber,map_sum,smoothSupportedTraceFiberAction_fiber]
  change (∑ i,∑ a,(e x a i*f i) • L a v) = ∑ a,traceModelLogGradient e r a x • L a v
  rw [Finset.sum_comm]
  simp_rw [traceModelLogGradient_eq_sum,Finset.sum_smul]
  rfl

end Actual

end CalderonN
