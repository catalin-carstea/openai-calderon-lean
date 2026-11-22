module

public import Proof.Manuscript.MovingTrace.ParametricLayerResidualPolynomial
public import Proof.CalderonPatch.BoundaryLayerCutoffEstimate
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

import Proof.CalderonPatch.BoundaryLayerTraceResponse

@[expose] public section

noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

open Set Filter Polynomial Finset
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Angular slice of a set of auxiliary parameters and angular coordinates. -/
def slice (U : Set (P × (EuclideanSpace ℝ (Fin n)))) (p : P) : Set (EuclideanSpace ℝ (Fin n)) := (fun x => (p,x)) ⁻¹' U

theorem isOpen_slice {U : Set (P × (EuclideanSpace ℝ (Fin n)))} (hU : IsOpen U) (p : P) : IsOpen (slice U p) :=
  hU.preimage (continuous_const.prodMk continuous_id)

theorem isClosed_slice {K : Set (P × (EuclideanSpace ℝ (Fin n)))} (hK : IsClosed K) (p : P) : IsClosed (slice K p) :=
  hK.preimage (continuous_const.prodMk continuous_id)

theorem contDiffOn_slice {K : Set (P × (EuclideanSpace ℝ (Fin n)))} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P × (EuclideanSpace ℝ (Fin n)) → F} (hf : ContDiffOn ℝ ∞ f K) (p : P) :
    ContDiffOn ℝ ∞ (fun x : (EuclideanSpace ℝ (Fin n)) => f (p,x)) (slice K p) :=
  hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (mapsTo_preimage _ _)

private theorem fderiv_layer_slice {U : Set (P × (EuclideanSpace ℝ (Fin n)))} (hU : IsOpen U)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P × (EuclideanSpace ℝ (Fin n)) → F} (hf : ContDiffOn ℝ ∞ f U) {p : P} {x : (EuclideanSpace ℝ (Fin n))} (hx : x ∈ slice U p)
    (w : (EuclideanSpace ℝ (Fin n))) :
    fderiv ℝ (fun y : (EuclideanSpace ℝ (Fin n)) => f (p,y)) x w = fderiv ℝ f (p,x) (0,w) := by
  let L : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (P × (EuclideanSpace ℝ (Fin n))) := ContinuousLinearMap.inr ℝ P (EuclideanSpace ℝ (Fin n))
  have hL : HasFDerivAt (fun x : (EuclideanSpace ℝ (Fin n)) => (p,x)) L x := by
    simpa [L,ContinuousLinearMap.inr] using (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  have hF := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  exact congrArg (fun A : (EuclideanSpace ℝ (Fin n)) →L[ℝ] F => A w) ((hF.hasFDerivAt.comp x hL).fderiv)

private theorem polynomialSpatialDeriv_slice {U : Set (P × (EuclideanSpace ℝ (Fin n)))} (hU : IsOpen U)
    {F : P × (EuclideanSpace ℝ (Fin n)) → ℂ[X]} (hF : CoeffContDiffOn F U) (D : ℕ) {p : P} {x : (EuclideanSpace ℝ (Fin n))}
    (hx : x ∈ slice U p) (w : (EuclideanSpace ℝ (Fin n))) :
    polynomialSpatialDeriv D w (fun y => F (p,y)) x = polynomialSpatialDeriv D (0,w) F (p,x) := by
  unfold polynomialSpatialDeriv
  apply sum_congr rfl
  intro k hk
  rw [fderiv_layer_slice hU (hF k) hx w]

theorem profileSpatialDeriv_slice {U : Set (P × (EuclideanSpace ℝ (Fin n)))} (hU : IsOpen U)
    {F : P × (EuclideanSpace ℝ (Fin n)) → ℂ[X]} (hF : CoeffContDiffOn F U)
    {κ : P × (EuclideanSpace ℝ (Fin n)) → ℝ} (hκ : ContDiffOn ℝ ∞ κ U)
    (D : ℕ) {p : P} {x : (EuclideanSpace ℝ (Fin n))} (hx : x ∈ slice U p) (w : (EuclideanSpace ℝ (Fin n))) :
    profileSpatialDeriv D w (fun y => κ (p,y)) (fun y => F (p,y)) x =
      profileSpatialDeriv D (0,w) κ F (p,x) := by
  rw [profileSpatialDeriv,profileSpatialDeriv,polynomialSpatialDeriv_slice hU hF D hx w,
    fderiv_layer_slice hU hκ hx w]

theorem profileSpatialDeriv_congr_fixed_kappa {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {F G : E → ℂ[X]} (h : EqOn F G U)
    (κ : E → ℝ) (D : ℕ) (w : E) :
    EqOn (profileSpatialDeriv D w κ F) (profileSpatialDeriv D w κ G) U :=
  profileSpatialDeriv_congr hU (fun _ _ => rfl) h D w


namespace ParametricLayerCoefficients

variable {U : Set (P × (EuclideanSpace ℝ (Fin n)))} (B : ParametricLayerCoefficients (n := n) U)

/-- At fixed geometry and frequency, the parametrized transport is the
published fixed-covector transport in its angular coordinates. -/
def angularSlice (p : P) (ξ : Fin n → ℝ)
    (hξ : ∀ (i : Fin n) (x : (EuclideanSpace ℝ (Fin n))), B.covector i (p,x) = (ξ i : ℂ)) :
    BoundaryLayerCoefficients ξ (slice (n := n) U p) := by
  refine {
    kappa := fun x => B.kappa (p,x)
    inverse := fun l i j x => B.inverse l i j (p,x)
    normalDrift := fun l x => B.normalDrift l (p,x)
    tangentDrift := fun l i x => B.tangentDrift l i (p,x)
    kappa_smooth := contDiffOn_slice B.kappa_smooth p
    kappa_pos := fun x hx => B.kappa_pos (p,x) hx
    inverse_smooth := fun l i j => contDiffOn_slice (B.inverse_smooth l i j) p
    inverse_symm := fun l i j x hx => B.inverse_symm l i j (p,x) hx
    normalDrift_smooth := fun l => contDiffOn_slice (B.normalDrift_smooth l) p
    tangentDrift_smooth := fun l i => contDiffOn_slice (B.tangentDrift_smooth l i) p
    principal_squared := ?_
  }
  intro x hx
  simpa only [hξ] using B.principal_squared (p,x) hx

theorem forcing_congr (hU : IsOpen U) (j k : ℕ) {F G : P × (EuclideanSpace ℝ (Fin n)) → ℂ[X]}
    (h : EqOn F G U) : EqOn (B.forcing j k F) (B.forcing j k G) U := by
  intro x hx
  have h₁ (i : Fin n) := profileSpatialDeriv_congr_fixed_kappa hU h B.kappa (2*k) (B.angularDirection i)
  have h₂ (i l : Fin n) :=
    profileSpatialDeriv_congr_fixed_kappa hU (h₁ l) B.kappa (2*k+1) (B.angularDirection i)
  simp [forcing,principalTerm,normalTerm,crossTerm,phaseDriftTerm,
    tangentSecondTerm,tangentFirstTerm,h hx,fun i => h₁ i hx,fun i l => h₂ i l hx]

theorem forcing_slice (hU : IsOpen U) (p : P) (ξ : Fin n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,(EuclideanSpace.single i 1))) (j k : ℕ)
    {F : P × (EuclideanSpace ℝ (Fin n)) → ℂ[X]} (hF : CoeffContDiffOn F U) {x : (EuclideanSpace ℝ (Fin n))} (hx : x ∈ slice U p) :
    B.forcing j k F (p,x) = (B.angularSlice p ξ hξ).forcing j k (fun y => F (p,y)) x := by
  have h₁ (i : Fin n) : EqOn (fun y => profileSpatialDeriv (2*k) (B.angularDirection i) B.kappa F (p,y))
      (profileSpatialDeriv (2*k) ((EuclideanSpace.single i 1)) (fun y => B.kappa (p,y)) (fun y => F (p,y)))
      (slice U p) := by
    intro y hy
    rw [hAxis i]
    exact (profileSpatialDeriv_slice hU hF B.kappa_smooth (2*k) hy ((EuclideanSpace.single i 1))).symm
  have h₂ (i l : Fin n) :
      profileSpatialDeriv (2*k+1) (B.angularDirection i) B.kappa
        (profileSpatialDeriv (2*k) (B.angularDirection l) B.kappa F) (p,x) =
      profileSpatialDeriv (2*k+1) ((EuclideanSpace.single i 1)) (fun y => B.kappa (p,y))
        (profileSpatialDeriv (2*k) ((EuclideanSpace.single l 1)) (fun y => B.kappa (p,y)) (fun y => F (p,y))) x := by
    let Q := profileSpatialDeriv (2*k) (B.angularDirection l) B.kappa F
    have hQ := hF.profileSpatialDeriv hU B.kappa_smooth (2*k) (B.angularDirection l)
    calc
      _ = profileSpatialDeriv (2*k+1) ((EuclideanSpace.single i 1)) (fun y => B.kappa (p,y)) (fun y => Q (p,y)) x := by
        rw [hAxis i]
        exact (profileSpatialDeriv_slice hU hQ B.kappa_smooth (2*k+1) hx ((EuclideanSpace.single i 1))).symm
      _ = _ := profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) (h₁ l) _ _ _ hx
  simp [forcing,principalTerm,normalTerm,crossTerm,phaseDriftTerm,tangentSecondTerm,tangentFirstTerm,
    BoundaryLayerCoefficients.forcing,BoundaryLayerCoefficients.principalTerm,BoundaryLayerCoefficients.normalTerm,
    BoundaryLayerCoefficients.crossTerm,BoundaryLayerCoefficients.phaseDriftTerm,
    BoundaryLayerCoefficients.tangentSecondTerm,BoundaryLayerCoefficients.tangentFirstTerm,angularSlice,
    hξ,fun i => h₁ i hx,fun i l => h₂ i l]

theorem layerPolynomial_slice (hU : IsOpen U) (p : P) (ξ : Fin n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,(EuclideanSpace.single i 1)))
    {K : Set (P × (EuclideanSpace ℝ (Fin n)))} (hK : IsClosed K) {a : P × (EuclideanSpace ℝ (Fin n)) → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    EqOn (fun x => B.layerPolynomial a j (p,x))
      ((B.angularSlice p ξ hξ).layerPolynomial (fun x => a (p,x)) j) (slice U p) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro x hx
    cases j with
    | zero =>
      exact (B.layerPolynomial_zero a (p,x)).trans
        ((B.angularSlice p ξ hξ).layerPolynomial_zero (fun x => a (p,x)) x).symm
    | succ j =>
      let C := B.angularSlice p ξ hξ
      change triangularLayerPolynomial B.transportScale a B.forcing (j + 1) (p,x) =
        triangularLayerPolynomial C.transportScale (fun y => a (p,y)) C.forcing (j + 1) x
      rw [triangularLayerPolynomial_succ,triangularLayerPolynomial_succ]
      dsimp only
      have hScale : C.transportScale x = B.transportScale (p,x) := rfl
      rw [hScale]
      refine congrArg (fixedDegreeTransport (B.transportScale (p,x)) (2*(j+1))) ?_
      refine congrArg Neg.neg ?_
      apply sum_congr rfl
      intro k hk
      let F := B.layerPolynomial a k.val
      let G := C.layerPolynomial (fun y => a (p,y)) k.val
      have hReg := (B.layerPolynomial_properties hU hK a ha ha0 k.val).1
      have hS := B.forcing_slice hU p ξ hξ hAxis (j+1) k.val hReg hx
      exact hS.trans (by
        have h : EqOn (fun z => F (p,z)) G (slice U p) := ih k.val k.isLt
        have h₁ (i : Fin n) :=
          profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) h C.kappa (2*k.val) ((EuclideanSpace.single i 1))
        have h₂ (i l : Fin n) :=
          profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) (h₁ l) C.kappa (2*k.val+1) ((EuclideanSpace.single i 1))
        change C.forcing (j+1) k.val (fun z => F (p,z)) x = C.forcing (j+1) k.val G x
        simp [BoundaryLayerCoefficients.forcing,BoundaryLayerCoefficients.principalTerm,
          BoundaryLayerCoefficients.normalTerm,BoundaryLayerCoefficients.crossTerm,
          BoundaryLayerCoefficients.phaseDriftTerm,BoundaryLayerCoefficients.tangentSecondTerm,
          BoundaryLayerCoefficients.tangentFirstTerm,h hx,fun i => h₁ i hx,fun i l => h₂ i l hx])

end ParametricLayerCoefficients
end CalderonPatch.BoundaryLayer
