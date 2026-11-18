import Proof.PhysicalPotentialWordCoreIdentity
import Proof.Archive.FiniteWordCorePolarization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFiniteWordPolarization
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def potentialForwardCoreValue (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (V : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ)) : SphereSobolev (1/2:ℝ) :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
    potentialWordCoefficient d y a b • P.potentialGeneratorHigh y a (V b)

def potentialReverseCoreValue (P : PhysicalPrincipalData Y d CF CT) {y : X} {CG CK : ℝ}
    (W : PhysicalPotentialQuarticData P y CG CK)
    (v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ)) : SphereSobolev (1/2:ℝ) :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
    potentialWordCoefficient d y a b • W.adjointHigh b (v a)

/-- Exact complete physical matrix norm-square identity conditional only on
explicit genuine first-word lifts; all49-by49 cross terms are included. -/
lemma potential_core_norm_difference (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u)
    (hv : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v a)=W.adjointHigh a u) :
    ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialForwardCoreValue y V)‖^2-
      ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialReverseCoreValue W v)‖^2=
      P.potentialQuarticWeakValue W u := by
  let p : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex → ℝ :=
    fun z => potentialWordCoefficient d y z.1 z.2
  let f : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex → SphereSobolev (1/2:ℝ) :=
    fun z => P.potentialGeneratorHigh y z.1 (V z.2)
  let r : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex → SphereSobolev (1/2:ℝ) :=
    fun z => W.adjointHigh z.2 (v z.1)
  let R : (PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex) →
      (PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex) → ℝ :=
    fun z w => polarizedQuarticWeakForm (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
      W.adjointHigh W.commLow W.commHigh z.2 z.1 w.1 w.2 u
  have hRow (z w : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex) :=
    P.potential_word_norm_pair_difference hy W u V v hV hv z.1 z.2 w.1 w.2
  have h := norm_weighted_word_sum_sq_sub (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) p f r R hRow
  simpa only [potentialForwardCoreValue,potentialReverseCoreValue,potentialQuarticWeakValue,
    finitePolarizedQuarticWeakForm,Fintype.sum_prod_type,p,f,r,R] using h

/-- The actual forward core value realizes exactly the original quadratic
balanced coefficient, through genuine Sobolev inclusions. -/
lemma potentialForwardCoreValue_balanced (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (u : SphereSobolev (3/2:ℝ))
    (V : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (P.potentialForwardCoreValue y V)=
      P.potentialQuadraticHalfL y u := by
  rw [potentialForwardCoreValue,P.potentialQuadraticHalfL_eq_word_matrix]
  simp only [potentialWordMatrixL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => potentialWordCoefficient d y a b • z)
  exact (DFunLike.congr_fun (P.potential_generator_balanced hy a) (V b)).trans
    (congrArg (P.potentialGeneratorLow y a) (hV b))

lemma abs_potential_core_norm_difference_small {Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    {CG CK : ℝ} (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u)
    (hv : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v a)=W.adjointHigh a u) :
    |‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialForwardCoreValue y V)‖^2-
      ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialReverseCoreValue W v)‖^2| ≤
      (4*CG^2*CK*(49*potentialWordEntryBudget K)^2)*ε*beta d.γ d.radius y*‖u‖^2 := by
  rw [P.potential_core_norm_difference hy W u V v hV hv]
  exact P.abs_potentialQuarticWeakValue_small hd hK hf hε hε1 hy hCG hCK hBudget W u
end PhysicalPrincipalData
end ShrinkingSpheres
