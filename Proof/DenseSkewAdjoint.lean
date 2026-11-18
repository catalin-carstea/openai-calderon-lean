import Proof.Archive.SphereSobolevInclusion
import Proof.Archive.SphereSobolevPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace ShrinkingSpheres

lemma true_adjoint_difference_skew {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (I : D →L[ℝ] E) (P Pa : D →L[ℝ] E)
    (hPair : ∀ u v,⟪P u,I v⟫_ℝ=⟪I u,Pa v⟫_ℝ) :
    ∀ u v,⟪(Pa-P) u,I v⟫_ℝ= -⟪I u,(Pa-P) v⟫_ℝ := by
  intro u v
  have hPa : ⟪Pa u,I v⟫_ℝ=⟪I u,P v⟫_ℝ :=
    (real_inner_comm _ _).trans ((hPair v u).symm.trans (real_inner_comm _ _))
  simp only [_root_.sub_apply,inner_sub_left,inner_sub_right,hPa,hPair u v]
  ring

lemma dense_skew_graph_adjoint {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I : D →L[ℝ] E) (hI : DenseRange I) (T : D →L[ℝ] E) (K : E →L[ℝ] E)
    (hGraph : K.comp I=T)
    (hSkew : ∀ u v,⟪T u,I v⟫_ℝ= -⟪I u,T v⟫_ℝ) : K.adjoint= -K := by
  have hCore (u v : D) : ⟪K (I u),I v⟫_ℝ= -⟪I u,K (I v)⟫_ℝ := by
    have hh (w : D) : K (I w)=T w := congrArg (fun A : D →L[ℝ] E => A w) hGraph
    rw [hh u,hh v]
    exact hSkew u v
  have hAll : ∀ u v : E,⟪K u,v⟫_ℝ= -⟪u,K v⟫_ℝ :=
    hI.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) hCore
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [K.adjoint_inner_right,_root_.neg_apply,inner_neg_right]
  exact hAll v u

lemma fderiv_skew_adjoint {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : V → E →L[ℝ] E) {U : Set V} (hU : IsOpen U) {p : V} (hp : p ∈ U)
    (hF : DifferentiableAt ℝ F p) (hSkew : ∀ q ∈ U,(F q).adjoint= -F q) (a : V) :
    (fderiv ℝ F p a).adjoint= -(fderiv ℝ F p a) := by
  let Adj : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).toContinuousLinearEquiv.toContinuousLinearMap
  have hEq : (fun q => Adj (F q)) =ᶠ[𝓝 p] (fun q => -F q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hSkew q hq
  have hLeft : HasFDerivAt (fun q => Adj (F q)) (Adj.comp (fderiv ℝ F p)) p :=
    Adj.hasFDerivAt.comp p hF.hasFDerivAt
  have hRight := hF.hasFDerivAt.neg
  have hEqD : fderiv ℝ (fun q => Adj (F q)) p=fderiv ℝ (fun q => -F q) p := hEq.fderiv_eq
  have hD : Adj.comp (fderiv ℝ F p)= -(fderiv ℝ F p) := hLeft.fderiv.symm.trans (hEqD.trans hRight.fderiv)
  exact congrArg (fun L : V →L[ℝ] (E →L[ℝ] E) => L a) hD
end ShrinkingSpheres
