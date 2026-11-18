import Proof.ClosedBoundaryMatrixMultiplier
import Proof.CommonSupportClosedAffineCoefficientFamily
import Proof.CommonSupportLowRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_le
    (k : Option I) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ l.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => boundaryMatrixMultiplier k (commonSupportMatrixFamily 2 a ha S hS hz t)) p‖ ≤
      (1404*boundaryHalfMultiplierBudget)*q := by
  let F := commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz
  have hEq : (fun t => boundaryMatrixMultiplier k (commonSupportMatrixFamily 2 a ha S hS hz t)) =
      fun t => closedBoundaryMatrixMultiplierL k (F t) := by
    funext t
    exact (closedBoundaryMatrixMultiplierL_eq_on_smooth k _).symm
  rw [hEq]
  apply norm_iteratedFDeriv_closedBoundaryMatrixMultiplier_le k F p
    (contDiff_commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz).contDiffAt n q hq
  exact hJets

/-- Every normal/tangent boundary Taylor jet retains the local true matrix
    affine residual; the same principal, flat and first-model witnesses occur. -/
theorem norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_affine_remainder_le
    (k : Option I) (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p) (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ l.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ q) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    ‖iteratedFDeriv ℝ n (fun t => boundaryMatrixMultiplier k (F t)-boundaryMatrixMultiplier k F0-
      r • boundaryMatrixMultiplier k (F1 t)) p‖ ≤ (1404*boundaryHalfMultiplierBudget)*q := by
  intro F F1
  let C := commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r
  have hC : ContDiffAt ℝ ∞ C p :=
    (contDiff_commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r).contDiffAt
  have hIncl (t : P) : C t = smoothCoefficientMatrixClosureInclusionL 2 (F t-F0-r • F1 t) := by
    rw [(smoothCoefficientMatrixClosureInclusionL 2).map_sub,
      (smoothCoefficientMatrixClosureInclusionL 2).map_sub,(smoothCoefficientMatrixClosureInclusionL 2).map_smul]
    rfl
  have hEq : (fun t => boundaryMatrixMultiplier k (F t)-boundaryMatrixMultiplier k F0-
      r • boundaryMatrixMultiplier k (F1 t)) = fun t => closedBoundaryMatrixMultiplierL k (C t) := by
    funext t
    have hInner := boundaryMatrixMultiplier_sub_smul k (F t) F0 1
    simp only [one_smul] at hInner
    have hOuter := boundaryMatrixMultiplier_sub_smul k (F t-F0) (F1 t) r
    have hAlgebra := hOuter.trans (congrArg
      (fun L => L-r • boundaryMatrixMultiplier k (F1 t)) hInner)
    rw [hIncl,closedBoundaryMatrixMultiplierL_eq_on_smooth]
    exact hAlgebra.symm
  rw [hEq]
  apply norm_iteratedFDeriv_closedBoundaryMatrixMultiplier_le k C p hC n q hq
  intro i j l x hx
  rw [commonSupportClosedAffineCoefficientFamily_jet_value a a1 aD ha ha1 S S1 hS hS1 hz hz1
    F0 r hField hFlat i j l x hx]
  exact hJets i j l x hx

end ShrinkingSpheres
