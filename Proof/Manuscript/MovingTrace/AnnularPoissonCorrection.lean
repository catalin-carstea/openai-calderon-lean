module

public import Proof.Manuscript.MovingTrace.FiniteCollarPoissonTrial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def transportCoefficient (a : Q × E → ℂ) (j : ℕ) (q : Q × E) : ℂ :=
  -C.coefficients.traceCoefficient a j q

theorem transportCoefficient_zero_of_notMem
    {K : Set (Q × E)} (hK : IsClosed K)
    (a : Q × E → ℂ) (ha : ContDiffOn ℝ ∞ a (baseDomain G)) (ha₀ : ∀ q ∉ K, a q = 0)
    (j : ℕ) {q : Q × E} (hq : q ∉ K) : C.transportCoefficient a j q = 0 := by
  simp [transportCoefficient,C.coefficients.traceCoefficient_eq_zero_of_notMem
    (baseDomain_open (G := G)) hK a ha ha₀ j hq]

theorem transportCoefficient_contDiffOn
    {K : Set (Q × E)} (hK : IsClosed K)
    (a : Q × E → ℂ) (ha : ContDiffOn ℝ ∞ a (baseDomain G)) (ha₀ : ∀ q ∉ K, a q = 0)
    (j : ℕ) : ContDiffOn ℝ ∞ (C.transportCoefficient a j) (baseDomain G) :=
  (C.coefficients.traceCoefficient_contDiffOn (baseDomain_open (G := G)) hK a ha ha₀ j).neg

theorem transportCoefficient_principal (a : Q × E → ℂ) (q : Q × E) :
    C.transportCoefficient a 0 q = (C.coefficients.kappa q : ℂ) * a q := by
  simp [transportCoefficient,C.coefficients.traceCoefficient_zero]

def dephase (h : ℝ) (q : Q × E) : ℂ :=
  (Complex.exp (Complex.I * ((ParametricLayerCoefficients.planePhase covector q)/h : ℝ)))⁻¹

theorem dephase_eq_exp (h : ℝ) (q : Q × E) :
    dephase h q = Complex.exp (Complex.I * ((-ParametricLayerCoefficients.planePhase covector q)/h : ℝ)) := by
  rw [dephase,← Complex.exp_neg]
  congr 1
  simp only [neg_div,Complex.ofReal_neg,mul_neg]

theorem dephase_contDiff (h : ℝ) : ContDiff ℝ ∞ (dephase (P := P) (n := n) h) := by
  have hEq : dephase (P := P) (n := n) h = _ := funext (dephase_eq_exp h)
  rw [hEq]
  exact (contDiff_const (c := Complex.I) |>.mul (Complex.ofRealCLM.contDiff.comp
    ((ParametricLayerCoefficients.planePhase_contDiff covector_contDiff).neg.div_const h))).cexp

theorem uniform_dephase_jets {K : Set (Q × E)} (hK : IsCompact K) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (dephase h) q‖ ≤ B*h⁻¹^N := by
  let φ : Q × E → ℝ := -ParametricLayerCoefficients.planePhase covector
  have hφ : ContDiff ℝ ∞ φ := (ParametricLayerCoefficients.planePhase_contDiff covector_contDiff).neg
  have hA (i : Fin (N+1)) : ∃ A ≥ 0, ∀ q ∈ K, ‖iteratedFDeriv ℝ i.val φ q‖ ≤ A := by
    obtain ⟨A,hA⟩ := hK.bddAbove_image
      ((hφ.continuous_iteratedFDeriv (by simp : (i.val : ℕ∞ω) ≤ ∞)).norm.continuousOn)
    exact ⟨max 0 A,le_max_left _ _,fun q hq => (hA ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose A hA hBound using hA
  let B := 1 + ∑ i : Fin (N+1), A i
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA i)
  refine ⟨(N.factorial:ℝ)*oscillatoryPhaseJetBound*B^N, by have := oscillatoryPhaseJetBound_nonneg; positivity,?_⟩
  intro q hq h hh hh₁ j hj
  rw [show dephase (P := P) (n := n) h =
    (fun q => Complex.exp (Complex.I * (φ q / h : ℝ))) from funext (dephase_eq_exp h)]
  refine norm_iteratedFDeriv_oscillatoryPhase_le (phase := φ) hφ.contDiffAt hB N
    (fun i _ hi => ?_) hh hh₁ j hj
  let k : Fin (N+1) := ⟨i,Nat.lt_succ_of_le hi⟩
  exact (hBound k q hq).trans ((Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ k)).trans
    (le_add_of_nonneg_left zero_le_one))

def normalizedPoissonResponse (a : Q × E → ℂ) (h : ℝ) (q : Q × E) : ℂ :=
  (h : ℂ) * dephase h q * G.angularPoissonReadout (angularPoint C.pole) (C.physicalDatum a h) q

variable {K : Set ((P × X n) × X n)} (hK : IsClosed K) (hKU : K ⊆ baseDomain G)
variable (a : (P × X n) × X n → ℂ) (ha : ContDiffOn ℝ ∞ a (baseDomain G)) (ha₀ : ∀ q ∉ K, a q = 0)
variable {Kx : Set (X n)} (hKx : IsCompact Kx) (hKproj : ∀ q ∈ K, q.2 ∈ Kx)

include hK hKU a ha ha₀ hKx hKproj in
theorem normalizedPoissonResponse_contDiffOn {h : ℝ} (hh : 0 < h) (hhδ : h ≤ C.δ/2) :
    ContDiffOn ℝ ∞ (C.normalizedPoissonResponse a h) ((G.V ×ˢ univ) ×ˢ univ) := by
  have hB (x : E) : angularPoint C.pole x ∈ closedBall (0:Z) 1 :=
    sphere_subset_closedBall ((stereographic' ((n+1)-1) C.pole).symm x).property
  obtain ⟨B,hB₀,hEstimate⟩ := G.uniform_angularPoisson_trial_residual
    («Q» := E) (J := (∅ : Set P)) isCompact_empty (empty_subset _)
      (angularPoint C.pole) (angularPoint_contDiff C.pole) hB (K := (∅ : Set E)) isCompact_empty 0
  have hReg := (hEstimate (C.physicalTrial a 0 h) (C.physicalDatum a h) (C.physicalResidual a 0 h)
    (C.physicalTrial_contDiff hK hKU a ha ha₀ hKx hKproj 0 h)
    (C.physicalResidual_contDiff hK hKU a ha ha₀ hKx hKproj 0 hh)
    (C.residualSupport Kx) (C.residualSupport_compact hKx)
    (C.physicalResidual_zero_off_support hK a ha ha₀ hKx hKproj 0 hh hhδ)
    (fun p hp => C.physicalTrial_eq_datum a 0 h p) (fun p hp => C.physicalResidual_eq_trial a 0 hh p)).1
  exact (contDiffOn_const.mul (dephase_contDiff h).contDiffOn).mul hReg

include hK hKU a ha ha₀ hKx hKproj in
/-- Solve the residual and read it at the boundary. Killing sufficiently
many transport terms offsets every fixed parameter derivative loss. -/
theorem normalizedPoissonResponse_full_finite_expansion
    {J : Set P} (hJ : IsCompact J) (hJV : J ⊆ G.V)
    {D : Set E} (hD : IsCompact D) (hD₀ : D ⊆ ({0}ᶜ : Set E))
    {Kout : Set E} (hOut : IsCompact Kout) (R N : ℕ) :
    let L := 2*N+n+4
    let M := R+3*L+N
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ, 0 < h → h ≤ C.δ/2 →
      ∀ p ∈ J, ∀ ν ∈ D, ∀ x ∈ Kout, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (fun q => C.normalizedPoissonResponse a h q -
          ∑ k ∈ Finset.range (M+1), (h : ℂ)^k * C.transportCoefficient a k q) ((p,ν),x)‖ ≤ B*h^R := by
  dsimp only
  let L := 2*N+n+4
  let M := R+3*L+N
  let U : Set (Q × E) := (G.V ×ˢ univ) ×ˢ univ
  let T := (J ×ˢ D) ×ˢ Kout
  have hU : IsOpen U := (G.openV.prod isOpen_univ).prod isOpen_univ
  have hV : J ×ˢ D ⊆ G.V ×ˢ ({0}ᶜ : Set E) := Set.prod_mono hJV hD₀
  have hB (x : E) : angularPoint C.pole x ∈ closedBall (0:Z) 1 :=
    sphere_subset_closedBall ((stereographic' ((n+1)-1) C.pole).symm x).property
  obtain ⟨B₁,hB₁,hResidual⟩ := C.uniform_physicalResidual_bound hK hKU a ha ha₀ hKx hKproj
    (hJ.prod hD) hV M L
  obtain ⟨B₂,hB₂,hSolve⟩ := G.uniform_angularPoisson_trial_residual
    («Q» := E) hJ hJV (angularPoint C.pole) (angularPoint_contDiff C.pole) hB hOut N
  obtain ⟨B₃,hB₃,hOsc⟩ := uniform_dephase_jets ((hJ.prod hD).prod hOut) N
  let Bmul := ContinuousLinearMap.mul ℝ ℂ
  refine ⟨‖Bmul‖*2^N*B₃*B₂*B₁,by positivity,?_⟩
  intro h hh hhδ p hp ν hν x hx j hj
  let q : Q × E := ((p,ν),x)
  have hqT : q ∈ T := ⟨⟨hp,hν⟩,hx⟩
  have hqU : q ∈ U := ⟨⟨hJV hp,mem_univ _⟩,mem_univ _⟩
  have hh₁ : h ≤ 1 := hhδ.trans (by linarith [C.small])
  let w : E → Z := angularPoint C.pole
  let trial (q : Q × E) := fderiv ℝ (fun z => C.physicalTrial a M h (q.1,z)) (w q.2) (w q.2)
  let exact' := G.angularPoissonReadout w (C.physicalDatum a h)
  let err := exact' - trial
  have hWave := C.physicalTrial_contDiff hK hKU a ha ha₀ hKx hKproj M h
  obtain ⟨hExact,hDiff⟩ := hSolve (C.physicalTrial a M h) (C.physicalDatum a h) (C.physicalResidual a M h)
    hWave (C.physicalResidual_contDiff hK hKU a ha ha₀ hKx hKproj M hh)
    (C.residualSupport Kx) (C.residualSupport_compact hKx)
    (C.physicalResidual_zero_off_support hK a ha ha₀ hKx hKproj M hh hhδ)
    (fun p _ => C.physicalTrial_eq_datum a M h p) (fun p _ => C.physicalResidual_eq_trial a M hh p)
  have hTrial : ContDiff ℝ ∞ trial := by
    let A := (continuousMultilinearCurryFin1 ℝ Z ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    have hMap : ContDiff ℝ ∞ (fun q : Q × E => (q.1,w q.2)) :=
      contDiff_fst.prodMk ((angularPoint_contDiff C.pole).comp contDiff_snd)
    have hJ := (contDiff_iteratedFDeriv_slice_right hWave 1).comp hMap
    apply contDiffOn_univ.mp
    apply ((A.contDiff.comp hJ).clm_apply ((angularPoint_contDiff C.pole).comp contDiff_snd)).contDiffOn.congr
    intro q _
    change trial q = iteratedFDeriv ℝ 1 (fun z => C.physicalTrial a M h (q.1,z)) (w q.2) (fun _ => w q.2)
    rw [iteratedFDeriv_one_apply]
  have hErr : ContDiffAt ℝ ∞ err q :=
    (hExact.contDiffAt (hU.mem_nhds hqU)).sub hTrial.contDiffAt
  let weight := h⁻¹^L * (h^(M+1)*h⁻¹^(2*L+2))
  have hWeight : 0 ≤ weight := by dsimp only [weight]; positivity
  have hE : ∀ i ≤ N, ‖iteratedFDeriv ℝ i err q‖ ≤ B₂*(B₁*weight) :=
    hDiff (p,ν) hp x hx _ (by positivity)
      (fun i hi z => hResidual h hh hhδ (p,ν) ⟨hp,hν⟩ z i hi)
  have hOscJ := hOsc q hqT h hh hh₁
  have hMul := ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound Bmul
    (dephase h) err q (dephase_contDiff h).contDiffAt hErr N
    (B₃*h⁻¹^N) (B₂*(B₁*weight)) (by positivity) (by positivity) hOscJ hE j hj
  have hEq : (fun q => C.normalizedPoissonResponse a h q -
          ∑ k ∈ Finset.range (M+1), (h : ℂ)^k * C.transportCoefficient a k q) =
      h • (fun q => dephase h q * err q) := by
    funext z
    simp only [transportCoefficient]
    rw [← C.physicalTrial_normal_readout hK hKU a ha ha₀ hKx hKproj M hh.ne' z]
    change (h:ℂ) * dephase h z * exact' z - (h:ℂ) * dephase h z * trial z =
      (h:ℂ) * (dephase h z * (exact' z - trial z))
    ring
  change ‖iteratedFDeriv ℝ j (fun q => C.normalizedPoissonResponse a h q -
      ∑ k ∈ Finset.range (M+1), (h : ℂ)^k * C.transportCoefficient a k q) q‖ ≤ _
  rw [hEq,iteratedFDeriv_const_smul_apply (((dephase_contDiff h).contDiffAt.mul hErr).of_le (by simp)),
    norm_smul,Real.norm_of_nonneg hh.le]
  refine (mul_le_mul_of_nonneg_left hMul hh.le).trans_eq ?_
  have hPow : h * (h⁻¹^N * weight) = h^R := by
    let k := N+L+(2*L+2)
    have he : 1+(M+1) = R+k := by dsimp only [M,k]; omega
    calc
      h*(h⁻¹^N*weight) = h^(1+(M+1)) * h⁻¹^k := by
        dsimp only [weight,k]
        simp only [pow_add,pow_one]
        ring
      _ = h^R := by
        rw [he,pow_add,mul_assoc,← mul_pow,mul_inv_cancel₀ hh.ne',one_pow,mul_one]
  calc
    _ = (‖Bmul‖*2^N*B₃*B₂*B₁)*(h*(h⁻¹^N*weight)) := by ring
    _ = _ := by rw [hPow]

end SignedPoissonCollar
end CalderonPaper
