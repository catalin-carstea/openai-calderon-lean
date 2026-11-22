module

public import Proof.Manuscript.MovingTrace.ParametricLayerSliceJet
public import Proof.Manuscript.MovingTrace.SplitOperatorLayerCoefficients
public import Proof.Manuscript.MovingTrace.FixedLayerResidualIdentity
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN Set Finset Polynomial
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

def planePhase (ξ : P → X n) (q : P × X n) : ℝ :=
  ∑ i : I n, ξ q.1 i * q.2 i

theorem planePhase_contDiff {ξ : P → X n} (hξ : ContDiff ℝ ∞ ξ) :
    ContDiff ℝ ∞ (planePhase ξ) := by
  apply ContDiff.sum
  intro i hi
  have hL := (EuclideanSpace.proj i : X n →L[ℝ] ℝ).contDiff (n := ∞)
  exact ((hL.comp hξ).comp contDiff_fst).mul (hL.comp contDiff_snd)

theorem tangentialPhaseRead_eq_planePhase (ξ : P → X n) (p : P) (h : ℝ) (x : X n) :
    tangentialPhaseRead (fun i => ξ p i) h x = planePhase ξ (p,x) / h := by
  simp only [tangentialPhaseRead, planePhase, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, PiLp.proj_apply, div_eq_mul_inv]
  ring

theorem finiteWave_joint_contDiff (hU : IsOpen U) {K : Set (P × X n)} (hK : IsClosed K) (hKU : K ⊆ U)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) {phase : P × X n → ℝ} (hp : ContDiff ℝ ∞ phase)
    (M : ℕ) (h : ℝ) : ContDiff ℝ ∞ (B.finiteWave a η phase M h) := by
  have hPhi : ContDiff ℝ ∞ (fun q : (P × X n) × ℝ => (phase q.1 / h : ℝ)) :=
    (hp.comp contDiff_fst).div_const h
  have hCast := Complex.ofRealCLM.contDiff.comp hPhi
  have hPhase : ContDiff ℝ ∞ (fun q : (P × X n) × ℝ => Complex.exp (Complex.I * (phase q.1 / h : ℝ))) :=
    (contDiff_const.mul hCast).cexp
  apply hPhase.mul
  apply ContDiff.sum
  intro j hj
  have hp := B.layerPolynomial_properties hU hK a ha ha0 j
  exact contDiff_const.mul (cutoffProfileFamily_contDiff hU hη B.kappa_smooth hp.1
    (2*j+1) (fun y hy => Nat.lt_succ_of_le (hp.2.1 y hy)) hK hKU hp.2.2 h)

theorem finiteWave_eq_slice (hU : IsOpen U) {K : Set (P × X n)} (hK : IsClosed K) (hKU : K ⊆ U)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (η : ℝ → ℝ) (ξ : P → X n) (p : P)
    (hξ : ∀ (i : I n) (x : X n), B.covector i (p,x) = (ξ p i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i)) (M : ℕ) (h : ℝ) :
    (fun q : X n × ℝ => B.finiteWave a η (planePhase ξ) M h ((p,q.1),q.2)) =
      (B.angularSlice p (fun i => ξ p i) hξ).finiteWave (fun x => a (p,x)) η M h := by
  let C := B.angularSlice p (fun i => ξ p i) hξ
  let a' := fun x => a (p,x)
  have ha' : ContDiffOn ℝ ∞ a' (slice U p) := contDiffOn_slice ha p
  have ha₀ : ∀ x ∉ slice K p, a' x = 0 := fun x hx => ha0 (p,x) hx
  have hPolynomial (j : ℕ) (x : X n) : B.layerPolynomial a j (p,x) = C.layerPolynomial a' j x := by
    by_cases hx : x ∈ slice U p
    · exact B.layerPolynomial_slice hU p (fun i => ξ p i) hξ hAxis hK ha ha0 j hx
    · have hxK : (p,x) ∉ K := fun h => hx (hKU h)
      exact ((B.layerPolynomial_properties hU hK a ha ha0 j).2.2 (p,x) hxK).trans
        (((C.layerPolynomial_properties (isOpen_slice hU p) (isClosed_slice hK p) a' ha' ha₀ j).2.2 x hxK).symm)
  funext q
  unfold finiteWave BoundaryLayerCoefficients.finiteWave
  have hExp : tangentialWave (fun i => ξ p i) h q.1 =
      Complex.exp (Complex.I * (planePhase ξ (p,q.1) / h : ℝ)) := by
    rw [tangentialWave,tangentialPhaseRead_eq_planePhase]
  rw [hExp]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (h ^ j : ℂ) * cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h ((p,q.1),q.2) =
    (h ^ j : ℂ) * cutoffProfileFamily η C.kappa (C.layerPolynomial a' j) h q
  have hκ : C.kappa q.1 = B.kappa (p,q.1) := rfl
  simp only [cutoffProfileFamily,polynomialProfileFamily,hPolynomial,hκ]

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
