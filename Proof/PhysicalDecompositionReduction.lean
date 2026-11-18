import Proof.PhysicalComparisonReduction
import Proof.RemainderAbsorption

noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

/-- The remaining physical decomposition at its actual output: the commutator error has
    the frozen energy bound and the Dirichlet remainder has the uniform H¹ bound. -/
def PhysicalDecomposition (Y : Set X) (d : Data) (φ : Field) (ε CE CJ : ℝ)
    (T Tf P : Output Y d) : Prop :=
  ∃ U Ud J : Output Y d,∃ err : ℝ,
    ‖(2:ℝ) • T+U‖^2-‖(2:ℝ) • Tf+Ud‖^2 = 4*(‖T‖^2-‖Tf‖^2)+err ∧
    |err| ≤ CE*ε*(energyNorm Y d φ)^2 ∧
    ‖J‖^2 ≤ CJ^2*(∫ y in Y,metricDensity d.γ y*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w))) ∧
    P = (2:ℝ) • T+U+J

/-- Only the physical operator estimates remain. All model and physical outputs in this
    premise are already constructed from the admitted geometry and test. -/
def UniformPhysicalDecomposition (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) : Prop :=
  ∃ B η CE CJ : ℝ,0 < η ∧ 0 ≤ CE ∧ 0 ≤ CJ ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D)
        (P : PhysicalOutputRealization Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ)),
        PhysicalDecomposition Y d φ ε CE CJ O.raisingOutput O.loweringOutput P.output

/-- The physical output's norm and the inverse-floor absorption are proved here; neither
    is part of the outstanding physical decomposition premise. -/
theorem uniformPhysicalComparison_of_decomposition {Y Ω : Set X} (hY : IsOpen Y) (hsub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} (hK : 0 < K)
    (hphysical : UniformPhysicalDecomposition Y Ω K ρ c₀ M Cj) :
    UniformPhysicalComparison Y Ω K ρ c₀ M Cj := by
  obtain ⟨B,η,CE,CJ,hη,hCE,hCJ,produce⟩ := hphysical
  refine ⟨max B 1,η,CE,CJ,hη,hCE,hCJ,?_⟩
  intro floor hfloor ε hε hsmall d hd φ hφ E D O
  have hf : 1 ≤ floor := (le_max_right ..).trans hfloor
  obtain ⟨P,hnorm⟩ := hd.exists_movingTraceOutput hY hsub hK hφ
  obtain ⟨U,Ud,J,err,hcomp,herr,hJ,hP⟩ :=
    produce floor ((le_max_left ..).trans hfloor) ε hε hsmall d hd φ hφ E D O P
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hsub,fun y hy => hd.1.1.2 y (hsub hy)⟩
  have he := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hsub
  have hframe := fun y hy => hd.1.2.2.2.2.2.2.2 y (hsub hy)
  exact ⟨U,Ud,J,P.output,err,hcomp,herr,
    remainder_norm_le_of_sobolev_one hY h hK he hframe hd.2.2.2.2.1 hf hφ J hCJ hJ,hP,hnorm⟩

theorem uniformEstimate_of_physicalDecomposition {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hc₀ : 0 < c₀) (hphysical : UniformPhysicalDecomposition Y Ω K ρ c₀ M Cj) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C :=
  uniformEstimate_of_physicalComparison hY hΩ hsub hm K ρ c₀ M Cj hK hc₀
    (uniformPhysicalComparison_of_decomposition hY hsub (zero_lt_one.trans_le hK) hphysical)

end ShrinkingSpheres
