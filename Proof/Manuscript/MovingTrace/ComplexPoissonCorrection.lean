module

public import Proof.Manuscript.MovingTrace.AngularNormalReadout
public import Proof.Manuscript.MovingTrace.ClassicalPoissonComparison
public import Proof.Manuscript.MovingTrace.CutTrialResidual
public import Proof.Manuscript.MovingTrace.MixedResidualSliceJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonN.BallDirichlet Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
variable {P Q E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth metric and one smooth bounded-support divergence coefficient
for its exact Dirichlet solve on a common geometric tube. -/
structure BallPoissonTube (P : Type) (dim : ℕ)
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  V : Set P
  openV : IsOpen V
  U : Set (P × X dim)
  openU : IsOpen U
  contains : V ×ˢ closedBall (0 : X dim) 1 ⊆ U
  g : P × X dim → Mat dim
  smoothG : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U
  posG : ∀ q ∈ U, (g q).PosDef
  a : P × X dim → Mat dim
  smoothA : ContDiff ℝ ∞ a
  supportA : Set (X dim)
  compactA : IsCompact supportA
  zeroA : ∀ p z, z ∉ supportA → a (p,z) = 0
  eqCoeff : ∀ q ∈ U, ∀ i j, a q i j = divergenceCoeff (fun z => g (q.1,z)) q.2 i j
  lo : P → ℝ
  hi : P → ℝ
  elliptic : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
    (fun z => a (p,z)) (lo p) (hi p)

namespace BallPoissonTube

variable (G : BallPoissonTube P (n+1))

def complexPoisson (d : (P × Q) × Z → ℂ) (p : P × Q) (z : Z) : ℂ :=
  ⟨fixedBallPoisson (fun y => G.g (p.1,y)) (fun y => (d (p,y)).re) z,
   fixedBallPoisson (fun y => G.g (p.1,y)) (fun y => (d (p,y)).im) z⟩

def angularPoissonReadout (w : E → Z) (d : (P × Q) × Z → ℂ) (q : (P × Q) × E) : ℂ :=
  fderiv ℝ (G.complexPoisson d q.1) (w q.2) (w q.2)

/-- The exact harmonic solution's radial readout differs from the trial by
the trace of the solved residual. All jets of the residual on a common
compact set are measured in the joint parameter-and-space norm. -/
theorem uniform_angularPoisson_trial_residual
    {J : Set P} (hJ : IsCompact J) (hJV : J ⊆ G.V)
    (w : E → Z) (hw : ContDiff ℝ ∞ w) (hwB : ∀ x, w x ∈ closedBall (0:Z) 1)
    {K : Set E} (hK : IsCompact K) (N : ℕ) :
    let L := 2*N+n+4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u d f : (P × Q) × Z → ℂ) (hu : ContDiff ℝ ∞ u)
      (hf : ContDiff ℝ ∞ f) (Kf : Set Z) (hKf : IsCompact Kf)
      (hSuppF : ∀ p z, z ∉ Kf → f (p,z) = 0)
      (hDatum : ∀ p : P × Q, p.1 ∈ G.V →
        EqOn (fun z => u (p,z)) (fun z => d (p,z)) (standardSphere (n+1)))
      (hEq : ∀ p : P × Q, p.1 ∈ G.V → EqOn
        (complexNegativeBallDivergence (fun z => G.a (p.1,z)) (fun z => u (p,z)))
        (fun z => f (p,z)) (ball (0 : Z) 1)),
      let trial (q : (P × Q) × E) := fderiv ℝ (fun z => u (q.1,z)) (w q.2) (w q.2)
      ContDiffOn ℝ ∞ (G.angularPoissonReadout w d) ((G.V ×ˢ univ) ×ˢ univ) ∧
      ∀ (p : P × Q), p.1 ∈ J → ∀ x ∈ K, ∀ M : ℝ, 0 ≤ M →
        (∀ j ≤ L, ∀ z : Z, ‖iteratedFDeriv ℝ j f (p,z)‖ ≤ M) →
        ∀ j ≤ N, ‖iteratedFDeriv ℝ j (G.angularPoissonReadout w d - trial) (p,x)‖ ≤ C*M := by
  dsimp only
  let T : Set ((P × Q) × E) := (G.V ×ˢ univ) ×ˢ univ
  have hT : IsOpen T := (G.openV.prod isOpen_univ).prod isOpen_univ
  obtain ⟨C₁,hC₁,hSolve⟩ := uniform_classical_zeroDirichlet_residual_angular_jets
    (Q := Q) G.openV hJ hJV G.a G.smoothA G.supportA G.compactA G.zeroA
    G.lo G.hi G.elliptic w hw hwB hK 1 N
  obtain ⟨C₂,hC₂,hRead⟩ := norm_normalJetReadout_on_compact hT hK w hw N
  let LR := Complex.ofRealCLM
  let LI := (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM
  refine ⟨(‖LR‖*‖Complex.reCLM‖ + ‖LI‖*‖Complex.imCLM‖) * C₂ * C₁,by positivity,?_⟩
  intro u d f hu hf Kf hKf hSuppF hDatum hEq
  let uR := Complex.reCLM ∘ u
  let uI := Complex.imCLM ∘ u
  let fR := Complex.reCLM ∘ f
  let fI := Complex.imCLM ∘ f
  have huR : ContDiff ℝ ∞ uR := Complex.reCLM.contDiff.comp hu
  have huI : ContDiff ℝ ∞ uI := Complex.imCLM.contDiff.comp hu
  have hfR : ContDiff ℝ ∞ fR := Complex.reCLM.contDiff.comp hf
  have hfI : ContDiff ℝ ∞ fI := Complex.imCLM.contDiff.comp hf
  obtain ⟨bR,hbR,hBR,hJetR,hBoundR⟩ := hSolve fR hfR Kf hKf
    (fun p z hz => by simp [fR,hSuppF p z hz])
  obtain ⟨bI,hbI,hBI,hJetI,hBoundI⟩ := hSolve fI hfI Kf hKf
    (fun p z hz => by simp [fI,hSuppF p z hz])
  let DR (q : (P × Q) × E) := iteratedFDeriv ℝ 1 (bR q.1) (w q.2)
  let DI (q : (P × Q) × E) := iteratedFDeriv ℝ 1 (bI q.1) (w q.2)
  let bReadR := normalJetReadout w DR
  let bReadI := normalJetReadout w DI
  have hMap : ContDiff ℝ ∞ (fun q : (P × Q) × E => (q.1,w q.2)) :=
    contDiff_fst.prodMk (hw.comp contDiff_snd)
  have hRange : MapsTo (fun q : (P × Q) × E => (q.1,w q.2)) T
      ((G.V ×ˢ univ) ×ˢ closedBall (0:Z) 1) := fun q hq => ⟨hq.1,hwB q.2⟩
  have hDR : ContDiffOn ℝ ∞ DR T := (hJetR 1).comp hMap.contDiffOn hRange
  have hDI : ContDiffOn ℝ ∞ DI T := (hJetI 1).comp hMap.contDiffOn hRange
  have hReadR : ContDiffOn ℝ ∞ bReadR T := normalJetReadout_contDiffOn hw hDR
  have hReadI : ContDiffOn ℝ ∞ bReadI T := normalJetReadout_contDiffOn hw hDI
  let t (q : (P × Q) × E) := fderiv ℝ (fun z => u (q.1,z)) (w q.2) (w q.2)
  have ht : ContDiff ℝ ∞ t := by
    let L := (continuousMultilinearCurryFin1 ℝ Z ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    have hJ := (contDiff_iteratedFDeriv_slice_right hu 1).comp hMap
    apply contDiffOn_univ.mp
    apply ((L.contDiff.comp hJ).clm_apply (hw.comp contDiff_snd)).contDiffOn.congr
    intro q hq
    change t q = iteratedFDeriv ℝ 1 (fun z => u (q.1,z)) (w q.2) (fun _ => w q.2)
    rw [iteratedFDeriv_one_apply]
  let err := (LR ∘ bReadR) + (LI ∘ bReadI)
  have hErr : ContDiffOn ℝ ∞ err T :=
    (LR.contDiff.comp_contDiffOn hReadR).add (LI.contDiff.comp_contDiffOn hReadI)
  have hExact : EqOn (G.angularPoissonReadout w d) (t - err) T := by
    rintro ⟨p,x⟩ hp
    let S : Set Z := (Prod.mk p.1) ⁻¹' G.U
    have hS : IsOpen S := G.openU.preimage (continuous_const.prodMk continuous_id)
    have hCS : closedBall (0 : Z) 1 ⊆ S := fun z hz => G.contains ⟨hp.1.1,hz⟩
    let g := fun z : Z => G.g (p.1,z)
    let a := fun z : Z => G.a (p.1,z)
    have hG : SmoothMetric S g :=
      ⟨fun i j => (G.smoothG i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun _ h => h),fun z hz => G.posG (p.1,z) hz⟩
    have ha : ContDiff ℝ ∞ a := G.smoothA.comp (contDiff_const.prodMk contDiff_id)
    have hCoeff : ∀ z ∈ S, ∀ i j, a z i j = divergenceCoeff g z i j :=
      fun z hz => G.eqCoeff (p.1,z) hz
    have hR := fixedBallPoisson_eq_trial_sub_residual hS hCS g a hG ha hCoeff
      (fun z => uR (p,z)) (bR p) (fun z => (d (p,z)).re) (fun z => fR (p,z))
      (huR.comp (contDiff_const.prodMk contDiff_id)) (hbR p)
      (fun z hz => congrArg Complex.re (hDatum p hp.1.1 hz)) (hBR p hp.1.1).1
      (fun z hz => congrArg Complex.re (hEq p hp.1.1 hz)) (hBR p hp.1.1).2
    have hI := fixedBallPoisson_eq_trial_sub_residual hS hCS g a hG ha hCoeff
      (fun z => uI (p,z)) (bI p) (fun z => (d (p,z)).im) (fun z => fI (p,z))
      (huI.comp (contDiff_const.prodMk contDiff_id)) (hbI p)
      (fun z hz => congrArg Complex.im (hDatum p hp.1.1 hz)) (hBI p hp.1.1).1
      (fun z hz => congrArg Complex.im (hEq p hp.1.1 hz)) (hBI p hp.1.1).2
    have hR' := congrArg (fun L : Z [×1]→L[ℝ] ℝ => L (fun _ => w x)) (hR.2 1 _ (hwB x))
    have hI' := congrArg (fun L : Z [×1]→L[ℝ] ℝ => L (fun _ => w x)) (hI.2 1 _ (hwB x))
    simp only [sub_apply,iteratedFDeriv_one_apply] at hR' hI'
    have huS : ContDiff ℝ ∞ (fun z => u (p,z)) := hu.comp (contDiff_const.prodMk contDiff_id)
    have hc : ContDiff ℝ ∞ (G.complexPoisson d p) := by
      change ContDiff ℝ ∞ (Complex.equivRealProdCLM.symm ∘ fun z =>
        (fixedBallPoisson g (fun y => (d (p,y)).re) z,
         fixedBallPoisson g (fun y => (d (p,y)).im) z))
      exact Complex.equivRealProdCLM.symm.contDiff.comp (hR.1.prodMk hI.1)
    have hDR' : bReadR (p,x) = fderiv ℝ (bR p) (w x) (w x) := normalJetReadout_iteratedFDeriv w bR _
    have hDI' : bReadI (p,x) = fderiv ℝ (bI p) (w x) (w x) := normalJetReadout_iteratedFDeriv w bI _
    have hCLM (L : ℂ →L[ℝ] ℝ) (f : Z → ℂ) (hf : ContDiff ℝ ∞ f) :
        fderiv ℝ (L ∘ f) (w x) (w x) = L (fderiv ℝ f (w x) (w x)) := by
      have h := (L.hasFDerivAt.comp (w x) (hf.differentiable (by simp) (w x)).hasFDerivAt).fderiv
      exact congrArg (fun A : Z →L[ℝ] ℝ => A (w x)) h
    change fderiv ℝ (G.complexPoisson d p) (w x) (w x) = t (p,x) - err (p,x)
    apply Complex.ext
    · change Complex.reCLM _ = _
      rw [← hCLM Complex.reCLM _ hc]
      change fderiv ℝ (fixedBallPoisson g (fun y => (d (p,y)).re)) (w x) (w x) = _
      rw [hR']
      change fderiv ℝ (Complex.reCLM ∘ fun z => u (p,z)) (w x) (w x) - _ = _
      rw [hCLM Complex.reCLM _ huS]
      simp [t,err,LR,LI,hDR']
    · change Complex.imCLM _ = _
      rw [← hCLM Complex.imCLM _ hc]
      change fderiv ℝ (fixedBallPoisson g (fun y => (d (p,y)).im)) (w x) (w x) = _
      rw [hI']
      change fderiv ℝ (Complex.imCLM ∘ fun z => u (p,z)) (w x) (w x) - _ = _
      rw [hCLM Complex.imCLM _ huS]
      simp [t,err,LR,LI,hDI']
  refine ⟨(ht.contDiffOn.sub hErr).congr hExact,?_⟩
  intro p hp x hx M hM hMjet j hj
  have hpT : (p,x) ∈ T := ⟨⟨hJV hp,mem_univ _⟩,mem_univ _⟩
  have hForcing (L₀ : ℂ →L[ℝ] ℝ) (i l : ℕ) (hi : i ≤ N) (hl : l ≤ N+n+4) (z : Z) :
      ‖iteratedFDeriv ℝ i (fun q => iteratedFDeriv ℝ l (fun y => (L₀ ∘ f) (q,y)) z) p‖ ≤
        ‖L₀‖*M := by
    exact (norm_mixedSlice_iteratedFDeriv_le (L₀.contDiff.comp hf) p z i l).trans
      ((L₀.norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
        (mul_le_mul_of_nonneg_left (hMjet (i+l) (by omega) z) (norm_nonneg _)))
  have hBR' : ∀ i ≤ N, ‖iteratedFDeriv ℝ i DR (p,x)‖ ≤ C₁*(‖Complex.reCLM‖*M) :=
    hBoundR p hp x hx _ (by positivity)
      (fun i hi l hl z => hForcing Complex.reCLM i l hi (by omega) z)
  have hBI' : ∀ i ≤ N, ‖iteratedFDeriv ℝ i DI (p,x)‖ ≤ C₁*(‖Complex.imCLM‖*M) :=
    hBoundI p hp x hx _ (by positivity)
      (fun i hi l hl z => hForcing Complex.imCLM i l hi (by omega) z)
  have hEqErr : EqOn (G.angularPoissonReadout w d - t) (-err) T :=
    fun q hq => by change G.angularPoissonReadout w d q - t q = -err q; rw [hExact hq]; change t q - err q - t q = -err q; abel
  change ‖iteratedFDeriv ℝ j (G.angularPoissonReadout w d - t) (p,x)‖ ≤ _
  rw [← iteratedFDerivWithin_of_isOpen j hT hpT,iteratedFDerivWithin_congr hEqErr hpT j,
    iteratedFDerivWithin_of_isOpen j hT hpT,iteratedFDeriv_neg_apply,norm_neg]
  change ‖iteratedFDeriv ℝ j ((LR ∘ bReadR) + (LI ∘ bReadI)) (p,x)‖ ≤ _
  have hRR := hRead DR hDR p x hx hpT _ (by positivity) hBR' j hj
  have hII := hRead DI hDI p x hx hpT _ (by positivity) hBI' j hj
  have hRight := hReadR.contDiffAt (hT.mem_nhds hpT)
  have hImag := hReadI.contDiffAt (hT.mem_nhds hpT)
  rw [iteratedFDeriv_add_apply (LR.contDiff.contDiffAt.comp _ hRight |>.of_le (by simp))
    (LI.contDiff.contDiffAt.comp _ hImag |>.of_le (by simp))]
  refine (norm_add_le _ _).trans ((add_le_add
    ((LR.norm_iteratedFDeriv_comp_left hRight (by simp)).trans (mul_le_mul_of_nonneg_left hRR (norm_nonneg _)))
    ((LI.norm_iteratedFDeriv_comp_left hImag (by simp)).trans (mul_le_mul_of_nonneg_left hII (norm_nonneg _)))).trans_eq ?_)
  ring

end BallPoissonTube
end CalderonPaper
