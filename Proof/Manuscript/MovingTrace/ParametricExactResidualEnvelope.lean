module

public import Proof.Manuscript.MovingTrace.CollarOperatorTaylorData
public import Proof.Manuscript.MovingTrace.JointSplitResidual
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 3400000

open CalderonN CalderonPaper Set
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

/-- On any fixed compact collar, arbitrarily many transport layers give
the indicated uniform decay of the actual split residual and all its
joint geometry/angular/depth jets through N. -/
theorem splitOperatorLayerCoefficients_residual_envelope
    {O : Set ((P × X n) × ℝ)} (hO : IsOpen O) {U : Set (P × X n)} (hU : IsOpen U)
    (hFace : MapsTo (fun p : P × X n => (p,(0:ℝ))) U O)
    (A : (P × X n) × ℝ → Mat n)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) O)
    (hSym : ∀ p ∈ O, ∀ i j, A p i j = A p j i)
    (hApos : ∀ p ∈ U, (A (p,0)).PosDef)
    (τ : (P × X n) × ℝ → ℝ) (hτ : ContDiffOn ℝ ∞ τ O)
    (b : (P × X n) × ℝ → I n → ℝ) (hb : ∀ i, ContDiffOn ℝ ∞ (fun p => b p i) O)
    (ξ : P → X n) (hξ : ContDiff ℝ ∞ ξ) (hξ₀ : ∀ p ∈ U, ξ p.1 ≠ 0)
    {K K₀ : Set (P × X n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hK₀ : IsClosed K₀) (hK₀U : K₀ ⊆ U)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K₀, a q = 0)
    {J : Set ((P × X n) × ℝ)} (hJ : IsCompact J)
    (hJK : ∀ q ∈ J, q.1 ∈ K)
    (hJseg : ∀ q ∈ J, ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ q ∈ O, q.2 < d → deriv η q.2 = 0 ∧ deriv (deriv η) q.2 = 0)
    (M N : ℕ) :
    let B := splitOperatorLayerCoefficients hO hFace A hA hSym hApos τ hτ b hb ξ hξ hξ₀
    let w (h : ℝ) := B.finiteWave a η (ParametricLayerCoefficients.planePhase ξ) M h
    let A' (q : (P × X n) × ℝ) := Matrix.of (fun i j => (A q i j : ℂ))
    let τ' (q : (P × X n) × ℝ) := (τ q : ℂ)
    let b' (q : (P × X n) × ℝ) (i : I n) := (b q i : ℂ)
    SmoothCollarContribution J (fun h => jointSplitOperator A' τ' b' (w h)) N
      (fun h => h^(M+1) * h⁻¹^(2*N+2)) := by
  dsimp only
  let B := splitOperatorLayerCoefficients hO hFace A hA hSym hApos τ hτ b hb ξ hξ hξ₀
  let A' (q : (P × X n) × ℝ) := Matrix.of (fun i j => (A q i j : ℂ))
  let τ' (q : (P × X n) × ℝ) := (τ q : ℂ)
  let b' (q : (P × X n) × ℝ) (i : I n) := (b q i : ℂ)
  let phase (q : (P × X n) × ℝ) := ParametricLayerCoefficients.planePhase ξ q.1
  let W := {q : (P × X n) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
  obtain ⟨hW,RA,Rτ,Rb,hRA,hRτ,hRb,hGap⟩ := splitOperatorLayerCoefficients_exists_TaylorRemainders
    hO hFace A hA hSym hApos τ hτ b hb ξ hξ hξ₀ M
  let T := W ∩ (U ×ˢ (univ : Set ℝ))
  have hT : IsOpen T := hW.inter (hU.prod isOpen_univ)
  have hTW : T ⊆ W := inter_subset_left
  have hTO : T ⊆ O := by
    intro q hq
    simpa only [one_mul,Prod.eta] using (show q ∈ W from hq.1) 1 (by simp)
  have hJT : J ⊆ T := fun q hq => ⟨hJseg q hq,hKU (hJK q hq),mem_univ _⟩
  have hτT : ContDiffOn ℝ ∞ τ' T := Complex.ofRealCLM.contDiff.comp_contDiffOn (hτ.mono hTO)
  have hDep := B.dephasedResidual_envelope hU hK hKU hK₀ a ha ha0 hT hJ hJT hJK inter_subset_right
    RA (fun i j => (hRA i j).mono hTW) Rτ τ' (hRτ.mono hTW) hτT Rb
    (fun i => (hRb i).mono hTW) η hη hd (fun q hq => hzero q (hTO hq)) M N
  apply oscillatoryResidual_envelope hT hJ hJT
    ((ParametricLayerCoefficients.planePhase_contDiff hξ).comp contDiff_fst).contDiffOn hDep
  intro h hh hh₁ q hq
  have hBξ (i : I n) (x : X n) : B.covector i (q.1.1,x) = (ξ q.1.1 i : ℂ) := rfl
  have hAxis (i : I n) : B.angularDirection i = (0,axis i) := rfl
  obtain ⟨hgA,hgτ,hgb⟩ := hGap q.1.1 q.1.2 q.2 hq.1
  exact B.splitResidual_eq_dephased hU q.1.1 ξ hBξ hAxis hK₀ hK₀U a ha ha0 η hη M A' τ' b'
    RA Rτ Rb hh.ne' hq.2.1 q.2 (fun i j => congrArg (fun t : ℝ => (t : ℂ)) (hSym q (hTO hq) i j))
    hgA hgτ hgb

end CalderonPatch.BoundaryLayer
