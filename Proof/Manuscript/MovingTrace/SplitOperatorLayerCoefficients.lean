module

public import Proof.Manuscript.MovingTrace.ParametricLayerSlice
public import Proof.Manuscript.MovingTrace.NormalTaylorFactor
public import Proof.CalderonN.MetricPair
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN Set Filter
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The coefficient of depth to the indicated power in the normal Taylor
polynomial of a scalar collar coefficient. -/
def collarTaylorCoefficient (a : (P × X n) × ℝ → ℝ) (k : ℕ)
    (p : P × X n) : ℂ :=
  ((iteratedDeriv k (fun t => a (p,t)) 0 : ℝ) : ℂ) / (k.factorial : ℂ)

theorem collarTaylorCoefficient_contDiffOn {O : Set ((P × X n) × ℝ)} (hO : IsOpen O)
    {a : (P × X n) × ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a O) {U : Set (P × X n)}
    (hFace : MapsTo (fun p : P × X n => (p,(0:ℝ))) U O) (k : ℕ) :
    ContDiffOn ℝ ∞ (collarTaylorCoefficient a k) U :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_normalTaylorCoeff hO ha hFace k)).div_const _

theorem collarTaylorCoefficient_congr {O : Set ((P × X n) × ℝ)} (hO : IsOpen O)
    {a b : (P × X n) × ℝ → ℝ} (hEq : EqOn a b O)
    (k : ℕ) {p : P × X n} (hp : (p,(0:ℝ)) ∈ O) :
    collarTaylorCoefficient a k p = collarTaylorCoefficient b k p := by
  have hGerm : (fun t => a (p,t)) =ᶠ[𝓝 0] fun t => b (p,t) := by
    have hMap : Continuous (fun t : ℝ => (p,t)) := continuous_const.prodMk continuous_id
    filter_upwards [hMap.continuousAt.preimage_mem_nhds (hO.mem_nhds hp)] with t ht
    exact hEq ht
  simp only [collarTaylorCoefficient,hGerm.iteratedDeriv_eq]

/-- Build the triangular transport data from the actual normalized
tangential principal matrix and drifts of a smooth signed collar. -/
def splitOperatorLayerCoefficients
    {O : Set ((P × X n) × ℝ)} (hO : IsOpen O) {U : Set (P × X n)}
    (hFace : MapsTo (fun p : P × X n => (p,(0:ℝ))) U O)
    (A : (P × X n) × ℝ → Mat n)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) O)
    (hSym : ∀ p ∈ O, ∀ i j, A p i j = A p j i)
    (hApos : ∀ p ∈ U, (A (p,0)).PosDef)
    (τ : (P × X n) × ℝ → ℝ) (hτ : ContDiffOn ℝ ∞ τ O)
    (b : (P × X n) × ℝ → I n → ℝ) (hb : ∀ i, ContDiffOn ℝ ∞ (fun p => b p i) O)
    (ξ : P → X n) (hξ : ContDiff ℝ ∞ ξ) (hξ₀ : ∀ p ∈ U, ξ p.1 ≠ 0) :
    ParametricLayerCoefficients (n := n) U := by
  let Q (p : P × X n) : ℝ := ∑ i : I n, ∑ j : I n, A (p,0) i j * ξ p.1 i * ξ p.1 j
  have hQ (p : P × X n) (hp : p ∈ U) : 0 < Q p := by
    let g : MetricField n := fun _ => A (p,0)
    change 0 < metricPair g 0 (ξ p.1) (ξ p.1)
    exact metricPair_pos_of_posDef (hApos p hp) (hξ₀ p hp)
  have hΞ (i : I n) : ContDiff ℝ ∞ (fun p : P × X n => ξ p.1 i) :=
    ((EuclideanSpace.proj i).contDiff.comp hξ).comp contDiff_fst
  have hQs : ContDiffOn ℝ ∞ Q U := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    exact (((hA i j).comp (contDiff_id.prodMk contDiff_const).contDiffOn hFace).mul
      (hΞ i).contDiffOn).mul (hΞ j).contDiffOn
  refine {
    angularDirection := fun i => (0,axis i)
    covector := fun i p => (ξ p.1 i : ℂ)
    covector_smooth := fun i => (Complex.ofRealCLM.contDiff.comp (hΞ i)).contDiffOn
    kappa := fun p => Real.sqrt (Q p)
    inverse := fun k i j => collarTaylorCoefficient (fun p => A p i j) k
    normalDrift := collarTaylorCoefficient τ
    tangentDrift := fun k i => collarTaylorCoefficient (fun p => b p i) k
    kappa_smooth := hQs.sqrt (fun p hp => (hQ p hp).ne')
    kappa_pos := fun p hp => Real.sqrt_pos.2 (hQ p hp)
    inverse_smooth := fun k i j => collarTaylorCoefficient_contDiffOn hO (hA i j) hFace k
    inverse_symm := fun k i j p hp => collarTaylorCoefficient_congr hO
      (fun _ hx => hSym _ hx i j) k (hFace hp)
    normalDrift_smooth := fun k => collarTaylorCoefficient_contDiffOn hO hτ hFace k
    tangentDrift_smooth := fun k i => collarTaylorCoefficient_contDiffOn hO (hb i) hFace k
    principal_squared := ?_
  }
  intro p hp
  have hSq : Real.sqrt (Q p) ^ 2 = Q p := Real.sq_sqrt (hQ p hp).le
  simp only [collarTaylorCoefficient,iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  exact_mod_cast hSq

end CalderonPatch.BoundaryLayer
