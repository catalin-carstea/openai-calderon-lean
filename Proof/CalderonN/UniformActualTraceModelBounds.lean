module

public import Proof.CalderonN.CoordinateTraceModelFactorBounds
public import Proof.CalderonN.ActualTraceBackgroundScalarJets
public import Proof.CalderonN.ActualTraceProfileScalarJets

import Proof.CalderonN.CoordinateJets
import Mathlib.Tactic

/-! Uniform bounds for the actual coordinate model on the same
angular basis as the velocity. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualCoordinateTraceModel_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K)
    (I₀ J : ℝ) (hI₀ : 1 ≤ I₀) (hJ : 1 ≤ J)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,∀ d : Data dim,Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (hg : Elliptic Y K d.γ) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
        (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y),
      ∀ x ∈ Y,∀ (R : Module.End ℝ (SmoothSphereTrace dim))
        (H : ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S) R J I₀),
      (actualCoordinateTraceModelFactors hY hg hK he hlog hA hEll S).Bounds H.atoms hY x (beta d.γ d.radius x) C := by
  obtain ⟨G,hG,hBg⟩ := uniform_actualTraceBackground_scalar_jets hΩ (by omega : 2+1 ≤ m) K hK M
  obtain ⟨P,hP,hProf⟩ := uniform_actualTraceProfile_scalar_jets hY hΩ hSub hm (by decide : 3 ≤ 8) K ρ c₀ M Cj hK
  let L := 2*I₀*I₀+(dim:ℝ)*(2*I₀*I₀)
  let C₀ := I₀+L+I₀*G+I₀*P
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hI := zero_le_one.trans hI₀
  have hG₀ := zero_le_one.trans hG
  have hP₀ := zero_le_one.trans hP
  have hIG := mul_nonneg hI hG₀
  have hIP := mul_nonneg hI hP₀
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  obtain ⟨C,hC,hBound⟩ := CoordinateTraceModelFactors.bounds_of_primitives (Y:=Y) (hn:=hn) C₀ hC₀
  refine ⟨C,hC,?_⟩
  intro floor hFloor ε d hd hFrame hg he hlog x hx R H
  let β := beta d.γ d.radius x
  let F := actualCoordinateTraceModelFactors (hn:=hn) hY hg hK he hlog hA hEll S
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hβ₀ := zero_le_one.trans hβ
  have h₁ : I₀ ≤ C₀ := by dsimp only [C₀]; linarith only [hL,hIG,hIP]
  have h₂ : L ≤ C₀ := by dsimp only [C₀]; linarith only [hI,hIG,hIP]
  have h₃ : I₀*G ≤ C₀ := by dsimp only [C₀]; linarith only [hI,hL,hIP]
  have h₄ : I₀*P ≤ C₀ := by dsimp only [C₀]; linarith only [hI,hL,hIG]
  have hBg' := hBg d.γ d.g₁ d.g₂ d.frame hd.1 hFrame x (hSub hx)
  have hP' := (hProf floor hFloor ε d hd x hx).2.2
  have hScalar (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) (h : LocalSmoothJetBudget f x 2 G) :
      PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 C₀ (PairedTraceFiberFamily.scalar hY f hf) :=
    (PairedTraceFiberFamilyBounds.ofScalar hx hβ₀ hI₀ H.identity f hf hG₀
      (fun n hn => (h.bound n hn).trans (le_mul_of_one_le_right hG₀ (one_le_pow₀ hβ)))).enlarge hβ₀ h₃
  refine hBound H.atoms hY x hx β hβ I₀ H.identity F ?_
  refine ⟨(PairedTraceFiberFamily.degree_bounds hA hEll S H hY x hx β hβ₀ 2).enlarge hβ₀ h₁,
    fun i j => (PairedTraceFiberFamily.rotation_bounds H hY x hx β hβ₀ 2 i j).enlarge hβ₀ h₁,
    fun i => (PairedTraceFiberFamily.raising_bounds hA hEll S H hJ hY x hx β hβ₀ 2 i).enlarge hβ₀ h₂,
    fun a i => hScalar _ _ (hBg'.1 i a),fun a i => hScalar _ _ (hBg'.2.1 i a),
    fun i a b => hScalar _ _ (hBg'.2.2 i a b),?_,?_,?_⟩
  · intro i
    have hf := contDiffOn_traceCoordinateLogGradient hY hlog i
    have h := PairedTraceFiberFamilyBounds.ofScalar (hY:=hY) (N:=2) hx hβ₀ hI₀ H.identity _ hf (mul_nonneg hP₀ hβ₀) (by
      intro n hn
      refine (hP' i n (by omega)).trans_eq ?_
      change P*β^(n+1) = (P*β)*β^n
      rw [pow_succ]
      ring)
    refine h.enlarge hβ₀ ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h₄ hβ₀
  · intro i j a b
    let f := traceCoordinateConnectionScalar d.γ d.frame j a b
    have hf := contDiffOn_traceCoordinateConnectionScalar hY hg hK he j a b
    have hf' : ContDiffOn ℝ ∞ (coordDeriv i f) Y :=
      (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    have h := PairedTraceFiberFamilyBounds.ofScalar (hY:=hY) (N:=1) hx hβ₀ hI₀ H.identity _ hf'
      (mul_nonneg hG₀ (sq_nonneg β)) (by
        intro n hn
        refine (norm_iteratedFDeriv_coordDeriv_le (hBg'.2.2 j a b).smooth i n).trans ?_
        exact ((hBg'.2.2 j a b).bound (n+1) (by omega)).trans
          ((le_mul_of_one_le_right hG₀ (one_le_pow₀ hβ)).trans
            (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hβ))))
    refine h.enlarge hβ₀ ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h₃ (sq_nonneg _)
  · intro i j
    let f := traceCoordinateLogGradient d.radius j
    have hf := contDiffOn_traceCoordinateLogGradient hY hlog j
    have hf' : ContDiffOn ℝ ∞ (coordDeriv i f) Y :=
      (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    have h := PairedTraceFiberFamilyBounds.ofScalar (hY:=hY) (N:=1) hx hβ₀ hI₀ H.identity _ hf'
      (mul_nonneg hP₀ (sq_nonneg β)) (by
        intro n hn
        refine (norm_iteratedFDeriv_coordDeriv_le (hf.contDiffAt (hY.mem_nhds hx)) i n).trans ?_
        refine (hP' j (n+1) (by omega)).trans_eq ?_
        change P*β^(n+1+1) = (P*β^2)*β^n
        rw [show n+1+1 = 2+n by omega,pow_add,mul_assoc])
    refine h.enlarge hβ₀ ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h₄ (sq_nonneg _)

end CalderonN
