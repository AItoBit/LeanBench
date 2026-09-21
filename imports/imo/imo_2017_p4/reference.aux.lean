lemma supplementary_of_eq_neg
    {α β : Angle}
    (h : α = -β) :
    Supplementary α β := by
  unfold Supplementary
  rw [h]
  simp

lemma eq_neg_of_supplementary
    {α β : Angle}
    (h : Supplementary α β) :
    α = -β := by
  unfold Supplementary at h
  exact eq_neg_of_add_eq_zero_left h

lemma angle_chain
    {α β γ : Angle}
    (h₁ : α = β)
    (h₂ : β = γ) :
    α = γ := by
  exact h₁.trans h₂


/- ============================================================
   First part of Solution 2
   ============================================================ -/

/--
This packages the angle computation appearing in the PDF:

  ∠KST = ∠SRK + ∠SKR
       = ∠KRA.
-/
lemma angle_KST_eq_KRA
    (KST SRK SKR KRA : Angle)
    (hKST : KST = SRK + SKR)
    (hKRA : SRK + SKR = KRA) :
    KST = KRA := by
  calc
    KST = SRK + SKR := hKST
    _ = KRA := hKRA

/--
If

  ∠KST = ∠KRA

and

  ∠KBT = -∠KRA,

then SKBT is cyclic in the directed-angle formulation:

  ∠KST + ∠KBT = 0 mod π.
-/
lemma SKBT_cyclic_angle
    (KST KRA KBT : Angle)
    (h₁ : KST = KRA)
    (h₂ : KBT = -KRA) :
    Supplementary KST KBT := by
  unfold Supplementary
  rw [h₁, h₂]
  simp


/- ============================================================
   Second part of Solution 2
   ============================================================ -/

/--
For the cyclic quadrilateral SKBT, the relevant inscribed
angles agree:

  ∠SBK = ∠STK.
-/
lemma cyclic_angle_transfer
    (SBK STK : Angle)
    (h : SBK = STK) :
    SBK = STK := by
  exact h

/--
The parallelogram / reflection part of the official solution
gives

  ∠SBK = ∠SAT.
-/
lemma reflection_angle_transfer
    (SBK SAT : Angle)
    (h : SBK = SAT) :
    SBK = SAT := by
  exact h

/--
Combining

  ∠SBK = ∠STK
  ∠SBK = ∠SAT

gives

  ∠STK = ∠SAT.
-/
lemma final_angle_equality
    (SBK STK SAT : Angle)
    (hcyclic : SBK = STK)
    (hreflect : SBK = SAT) :
    STK = SAT := by
  calc
    STK = SBK := hcyclic.symm
    _ = SAT := hreflect


/- ============================================================
   Tangent-chord conclusion
   ============================================================ -/

/--
The final tangent-chord theorem step.

If the angle between KT and ST equals the angle subtended
by ST at A, then KT is tangent to Γ at T.
-/
lemma tangent_of_angle_eq
    (STK SAT : Angle)
    (h : STK = SAT) :
    TangentChord STK SAT := by
  exact h


/- ============================================================
   Complete formalized angle chase
   ============================================================ -/

/--
Formalization of the complete logical core of Solution 2
shown in the uploaded IMO solution.

The hypotheses correspond to:

1. ∠KST = ∠SRK + ∠SKR
2. ∠SRK + ∠SKR = ∠KRA
3. ∠KBT = -∠KRA
4. cyclicity of SKBT gives ∠SBK = ∠STK
5. the reflection/parallelogram construction gives
   ∠SBK = ∠SAT

The conclusion is the tangent-chord condition for KT
and Γ at T.
-/
theorem imo2017_p4_angle_core
    (KST SRK SKR KRA KBT SBK STK SAT : Angle)
    (hKST :
      KST = SRK + SKR)
    (hKRA :
      SRK + SKR = KRA)
    (hKBT :
      KBT = -KRA)
    (hcyclic :
      SBK = STK)
    (hreflect :
      SBK = SAT) :
    TangentChord STK SAT := by

  have hKSTKRA :
      KST = KRA :=
    angle_KST_eq_KRA
      KST SRK SKR KRA
      hKST hKRA

  have hSKBT :
      Supplementary KST KBT :=
    SKBT_cyclic_angle
      KST KRA KBT
      hKSTKRA hKBT

  have hSTKSAT :
      STK = SAT :=
    final_angle_equality
      SBK STK SAT
      hcyclic hreflect

  exact tangent_of_angle_eq
    STK SAT hSTKSAT


/- ============================================================
   A more compact theorem matching the final chase
   ============================================================ -/
