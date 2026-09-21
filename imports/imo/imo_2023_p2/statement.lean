theorem candidate
    {ECircle : Type*}

    (ECollinear :
      EPoint → EPoint → EPoint → Prop)

    (ETangentAt :
      ECircle → EPoint → EPoint → Prop)

    (EInternalBisector :
      EPoint → EPoint → EPoint → EPoint → Prop)

    {A B C S P H : EPoint}
    {ω : ECircle}

    (hBS :
      ECollinear B S H)

    (hbis :
      EInternalBisector A B C H)

    (hPH_AH :
      dist P H =
        dist A H)

    (perp_to_tangent :
      OnPerpBisector
          (fun X Y : EPoint => dist X Y)
          H A P →
      ETangentAt ω P H) :

    Target
      ECollinear
      ETangentAt
      EInternalBisector
      A B C S P ω :=
