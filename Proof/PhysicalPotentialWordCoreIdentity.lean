import Proof.Archive.DoubleQuarticCoreIdentity
import Proof.PhysicalPotentialQuarticCaller
import Proof.BoundaryNegativePairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDoubleQuarticIdentity
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- SAME actual quadratic word norm difference, on a true common core.
The only extra inputs are explicit H3/2 lifts of all first words and their
adjoints, identified by the genuine H3/2-to-H1/2 inclusion. -/
lemma potential_word_norm_pair_difference (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u)
    (hv : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v a)=W.adjointHigh a u)
    (a b c e : PhysicalPotentialGeneratorIndex) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialGeneratorHigh y a (V b)),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialGeneratorHigh y c (V e))⟫_ℝ-
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W.adjointHigh b (v a)),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W.adjointHigh e (v c))⟫_ℝ=
      polarizedQuarticWeakForm (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
        W.adjointHigh W.commLow W.commHigh b a c e u := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let PL : SphereSobolev (1/2:ℝ) →L[ℝ] (SphereSobolev (-(1/2:ℝ)) →L[ℝ] ℝ) := innerSL ℝ
  let AL := P.potentialGeneratorLow y
  let BL := fun i => (AL i).adjoint
  let A := P.potentialGeneratorHigh y
  let B := W.adjointHigh
  have hA (i : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) : J (A i x)=AL i (I x) :=
    DFunLike.congr_fun (P.potential_generator_balanced hy i) x
  have hB (i : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) : J (B i x)=BL i (I x) :=
    DFunLike.congr_fun (W.adjoint_compatible i) x
  have hPivot (i : PhysicalPotentialGeneratorIndex) (x z : SphereSobolev (1/2:ℝ)) :
      PL x (AL i z)=PL z (BL i x) :=
    (ContinuousLinearMap.adjoint_inner_left (AL i) z x).symm.trans (real_inner_comm _ _)
  have hPair (x z : SphereSobolev (1/2:ℝ)) : PL x (J z)=⟪K x,K z⟫_ℝ := by
    have h := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2:ℝ) (by norm_num) z x
    exact (real_inner_comm _ _).trans (h.trans (real_inner_comm _ _))
  have hAdj := high_pairings_of_low_pivot I J K PL A B AL BL hA hB hPivot hPair
  have hG (i j : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) :
      J (W.commHigh i j x)=BL i (A j x)-AL j (B i x) :=
    (DFunLike.congr_fun (W.commutator_compatible i j) x).symm
  have hCl (i j : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) :
      W.commLow i j (I x)=J (W.commHigh i j x) :=
    (DFunLike.congr_fun (W.commutator_balanced i j) x).symm
  have h := double_word_pairing_sub_reverse_eq_four_pairings I J K PL A B AL BL W.commHigh W.commLow
    (sphereSobolevInclusionL_injective _ _ _) hA hB hG hCl hAdj.1 hAdj.2 hPair u V v hV hv a b c e
  have h1 : PL (A b u) (W.commLow a c (A e u))=
      sphereSobolevDualPairing (-(1/2:ℝ)) (W.commLow a c (A e u)) (A b u) := by
    change ⟪A b u,W.commLow a c (A e u)⟫_ℝ=⟪W.commLow a c (A e u),A b u⟫_ℝ
    exact real_inner_comm _ _
  have h2 : PL (A b u) (AL c (W.commHigh a e u))=
      sphereSobolevDualPairing (-(1/2:ℝ)) (AL c (W.commHigh a e u)) (A b u) := by
    change ⟪A b u,AL c (W.commHigh a e u)⟫_ℝ=⟪AL c (W.commHigh a e u),A b u⟫_ℝ
    exact real_inner_comm _ _
  have h3 : PL (W.commHigh c b u) (AL e (B a u))=
      sphereSobolevDualPairing (-(1/2:ℝ)) (AL e (B a u)) (W.commHigh c b u) := by
    change ⟪W.commHigh c b u,AL e (B a u)⟫_ℝ=⟪AL e (B a u),W.commHigh c b u⟫_ℝ
    exact real_inner_comm _ _
  have h4 : PL (B c u) (W.commLow b e (B a u))=
      sphereSobolevDualPairing (-(1/2:ℝ)) (W.commLow b e (B a u)) (B c u) := by
    change ⟪B c u,W.commLow b e (B a u)⟫_ℝ=⟪W.commLow b e (B a u),B c u⟫_ℝ
    exact real_inner_comm _ _
  exact h.trans (congrArg₂ (fun x z : ℝ => x+z)
    (congrArg₂ (fun x z : ℝ => x+z) (congrArg₂ (fun x z : ℝ => x+z) h1 h2) h3) h4)
end PhysicalPrincipalData
end ShrinkingSpheres
