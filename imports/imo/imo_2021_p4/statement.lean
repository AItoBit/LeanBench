theorem candidate
    {A C D T X Y Z P M Q N : EPoint}

    (hTX :
      dist T X = dist Z Y)

    (hL :
      dist A D + dist D T + dist X A
        =
      dist X P + dist T M)

    (hR :
      dist C D + dist D Y + dist Z C
        =
      dist Q Z + dist N Y)

    (hTM :
      dist T M = dist Q Z)

    (hXP :
      dist X P = dist N Y) :

    dist A D + dist D T + dist T X + dist X A
      =
    dist C D + dist D Y + dist Y Z + dist Z C :=
