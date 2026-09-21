theorem candidate
    (KST SRK SKR KRA KBT SBK STK SAT : Angle)
    (h₁ : KST = SRK + SKR)
    (h₂ : SRK + SKR = KRA)
    (h₃ : KBT = -KRA)
    (h₄ : SBK = STK)
    (h₅ : SBK = SAT) :
    TangentChord STK SAT :=
