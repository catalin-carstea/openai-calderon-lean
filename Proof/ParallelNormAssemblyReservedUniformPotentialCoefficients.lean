import Proof.ParallelNormAssemblyReservedNormalizedCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

lemma normalized_potential_coefficients_smooth {Y : Set X} (hY : IsOpen Y) {d : Data}
    (hR : ContDiffOn ℝ ∞ d.radius Y) (hRadius : ∀ x ∈ Y,0 < d.radius x)
    (hP : ∀ a b : I,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x a b) Y)
    (hQ : ∀ a b : I,ContDiffOn ℝ ∞ (fun x => (d.γ x)⁻¹ a b) Y)
    (a b : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (fun x => normalizedPotentialWordCoefficient d x a b) Y := by
  have hLogs := hR.log (fun x hx => (hRadius x hx).ne')
  have hFs (a : I) := contDiffOn_coordDeriv hY hLogs a
  have hSs (a b : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hR.mul (hP a b)
  have hEs (a b : I) : ContDiffOn ℝ ∞
      (fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))) Y := by
    simpa only [potentialCoordinateWordCoefficient,Matrix.sub_apply,div_eq_mul_inv,Pi.inv_apply] using
      ((hP a b).sub (hQ a b)).mul (hR.inv (fun x hx => (hRadius x hx).ne'))
  have hBody : ContDiffOn ℝ ∞ (fun x => normalizedPotentialCoefficientBody d x a b) Y := by
    rcases a with u | (a | a) <;> rcases b with v | (b | b)
    all_goals try dsimp only [normalizedPotentialCoefficientBody]
    · exact ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ((hSs a b).mul (hFs a)).mul (hFs b)))
    · exact contDiffOn_const
    · exact ContDiffOn.sum (fun a _ => (hR.mul (hSs a b)).mul (hFs a))
    · exact contDiffOn_const.mul (ContDiffOn.sum (fun b _ => (hR.mul (hEs a b)).mul (hFs b)))
    · exact hEs a b
    · exact hSs a b
    · exact ContDiffOn.sum (fun b _ => (hR.mul (hSs a b)).mul (hFs b))
    · exact hSs a b
    · exact (hR.mul hR).mul (hSs a b)
  exact hBody.congr (fun x hx => normalized_potential_coefficient_body d x (hRadius x hx).ne' a b)

/-- The complete actual potential's normalized scalar word matrix has
smooth coefficients and uniform linear-epsilon jets through two. The
constants precede every admitted profile and arbitrary smooth frame. -/
theorem uniform_normalized_potential_coefficients_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d →
    (∀ a b : PhysicalPotentialGeneratorIndex,
      ContDiffOn ℝ ∞ (fun x => normalizedPotentialWordCoefficient d x a b) Y) ∧
    ∀ y ∈ Y,∀ a b : PhysicalPotentialGeneratorIndex,
      ScalarTwoJetBound (fun x => normalizedPotentialWordCoefficient d x a b) y
        (beta d.γ d.radius y) (C*ε) := by
  obtain ⟨Cr,Cl,Cp,Ce,hCr,hCl,hCp,hCe,hInputs⟩ :=
    uniform_potential_scalar_inputs_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  let C := 144*Cp*Cl^2+96*Cr*Ce*Cl+48*Cr*Cp*Cl+16*Cr^2*Cp+Cp+Ce
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd
  have hR := hd.2.2.2.2.1.1
  have hRadius (x : X) (hx : x ∈ Y) := (hd.2.2.2.2.1.2 x hx).1
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun a b => (hd.1.2.2.1.1 a b).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hP (a b : I) := contDiffOn_principal_entry hg hg2 (zero_lt_one.trans_le hK) a b
  have hQ (a b : I) := hg.contDiffOn_inverse_entry (zero_lt_one.trans_le hK) a b
  refine ⟨normalized_potential_coefficients_smooth hY hR hRadius hP hQ,?_⟩
  intro y hy a b
  obtain ⟨hRad,hLog,hScalar,hPure⟩ := hInputs floor hf ε hε hε1 d hd y hy
  exact normalized_potential_coefficient_two_jets_of_inputs hY hy hR hRadius hP hQ hCr hCl hCp hCe hε
    (hf.trans (hd.2.2.2.2.1.2 y hy).2.1) hRad hLog hScalar hPure a b

end ShrinkingSpheres.ParallelEnergy
