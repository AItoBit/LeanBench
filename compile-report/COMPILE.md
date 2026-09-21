# Compilacion de referencias

Carpeta: `imports/imo` | referencias: 348

| Estado | Cantidad |
| ------ | -------- |
| `accepted` | 326 |
| `compile_error` | 21 |
| `timeout` | 1 |

Contextos del participante que NO compilan: **5**

## Fallos

| Problema | Cat. | Estado | Segundos | Contexto | Detalle |
| -------- | ---- | ------ | -------- | -------- | ------- |
| imo_1959_p2 | C | `compile_error` | 9.377 | ok | 143:20: error(lean.invalidField): Invalid field `parts`: The environment does not contain `Function.parts`, so it is not possible to project the field `parts` from an expression |
| imo_1964_p1 | C | `compile_error` | 5.742 | ok | 85:13: error(lean.invalidField): Invalid field `parts`: The environment does not contain `And.parts`, so it is not possible to project the field `parts` from an expression |
| imo_1976_p3 | C | `timeout` | 600.733 | ok | no se encontro la salida de '#print axioms Imo1976P3.candidate': la declaracion esperada no existe o no compilo |
| imo_1977_p4 | C | `compile_error` | 11.834 | ok | 78:4: error: Type mismatch |
| imo_1979_p6 | C | `compile_error` | 8.079 | ok | 139:71: error: unsolved goals |
| imo_1982_p2 | C | `compile_error` | 6.735 | ok | 21:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| imo_1983_p4 | C | `accepted` | 10.095 | error: invalid 'include', variable `hAB` has not been declar |  |
| imo_1990_p3 | C | `compile_error` | 8.741 | ok | 62:37: error: ring failed, ring expressions not equal |
| imo_1993_p6 | C | `accepted` | 7.266 | error: /tmp/leanbench_refs_lvfsmdho/context_checks/imo_1993_ |  |
| imo_1995_p6 | C | `compile_error` | 8.003 | ok | 217:73: error: unsolved goals |
| imo_1996_p1 | C | `compile_error` | 10.027 | ok | 150:30: error: ring failed, ring expressions not equal |
| imo_1998_p3 | C | `compile_error` | 8.85 | ok | 87:6: error: No goals to be solved |
| imo_1999_p4 | C | `compile_error` | 8.055 | ok | 26:4: error: ring failed, ring expressions not equal |
| imo_2000_p2 | C | `compile_error` | 5.666 | ok | 10:9: error(lean.unknownIdentifier): Unknown identifier `le_or_lt` |
| imo_2000_p4 | C | `accepted` | 14.242 | error: /tmp/leanbench_refs_lvfsmdho/context_checks/imo_2000_ |  |
| imo_2004_p4 | C | `compile_error` | 23.192 | ok | 27:8: error: No goals to be solved |
| imo_2004_p5 | C | `compile_error` | 41.016 | ok | 55:27: error: linarith failed to find a contradiction |
| imo_2005_p4 | A | `compile_error` | 6.4 | ok | 197:10: error: not a positivity goal |
| imo_2008_p3 | C | `compile_error` | 8.798 | ok | 19:4: error: ring failed, ring expressions not equal |
| imo_2008_p5 | C | `compile_error` | 9.16 | ok | 107:2: error: unsolved goals |
| imo_2010_p3 | C | `compile_error` | 7.614 | ok | 498:0: error: unterminated comment |
| imo_2010_p5 | C | `compile_error` | 10.464 | ok | 681:18: error: unexpected identifier; expected 'in' |
| imo_2014_p2 | C | `accepted` | 7.46 | error: unexpected token 'end'; expected ':=', 'where' or '|' |  |
| imo_2014_p4 | C | `accepted` | 7.554 | error: unexpected token 'end'; expected ':=', 'where' or '|' |  |
| imo_2017_p1 | C | `compile_error` | 6.67 | ok | 58:9: error: Tactic `unfold` failed: did not unfold 'IMO2017P1.IsSquare' |
| imo_2017_p6 | C | `compile_error` | 8.926 | ok | 263:46: error: unsolved goals |
| imo_2018_p1 | C | `compile_error` | 38.256 | ok | 229:37: error: (deterministic) timeout at `«Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.getTableauImp»`, maximum number of heartbeats (200000) has been reached |

## Todos

| Problema | Estado | Segundos |
| --- | --- | --- |
| imo_1959_p1 | `accepted` | 8.473 |
| imo_1959_p2 | `compile_error` | 9.377 |
| imo_1959_p3 | `accepted` | 9.258 |
| imo_1959_p4 | `accepted` | 3.845 |
| imo_1960_p1 | `accepted` | 8.638 |
| imo_1960_p2 | `accepted` | 7.088 |
| imo_1961_p1 | `accepted` | 16.353 |
| imo_1961_p3 | `accepted` | 8.1 |
| imo_1962_p1 | `accepted` | 6.41 |
| imo_1962_p2 | `accepted` | 17.579 |
| imo_1963_p1 | `accepted` | 11.918 |
| imo_1963_p4 | `accepted` | 7.944 |
| imo_1963_p5 | `accepted` | 8.102 |
| imo_1964_p1 | `compile_error` | 5.742 |
| imo_1964_p2 | `accepted` | 7.931 |
| imo_1964_p4 | `accepted` | 7.924 |
| imo_1965_p1 | `accepted` | 9.156 |
| imo_1965_p2 | `accepted` | 8.127 |
| imo_1965_p3 | `accepted` | 6.377 |
| imo_1965_p4 | `accepted` | 9.39 |
| imo_1965_p5 | `accepted` | 8.243 |
| imo_1965_p6 | `accepted` | 6.766 |
| imo_1966_p1 | `accepted` | 7.007 |
| imo_1966_p2 | `accepted` | 8.855 |
| imo_1966_p3 | `accepted` | 30.437 |
| imo_1966_p4 | `accepted` | 10.624 |
| imo_1966_p5 | `accepted` | 7.885 |
| imo_1966_p6 | `accepted` | 14.677 |
| imo_1967_p1 | `accepted` | 7.407 |
| imo_1967_p2 | `accepted` | 8.111 |
| imo_1967_p3 | `accepted` | 7.139 |
| imo_1967_p4 | `accepted` | 6.322 |
| imo_1967_p5 | `accepted` | 6.978 |
| imo_1967_p6 | `accepted` | 7.2 |
| imo_1968_p1 | `accepted` | 7.994 |
| imo_1968_p2 | `accepted` | 7.552 |
| imo_1968_p3 | `accepted` | 5.782 |
| imo_1968_p4 | `accepted` | 6.92 |
| imo_1968_p5 | `accepted` | 27.585 |
| imo_1968_p6 | `accepted` | 9.19 |
| imo_1969_p1 | `accepted` | 12.003 |
| imo_1969_p2 | `accepted` | 5.931 |
| imo_1969_p3 | `accepted` | 7.494 |
| imo_1969_p4 | `accepted` | 7.048 |
| imo_1969_p5 | `accepted` | 20.739 |
| imo_1969_p6 | `accepted` | 21.962 |
| imo_1970_p1 | `accepted` | 5.698 |
| imo_1970_p2 | `accepted` | 7.229 |
| imo_1970_p3 | `accepted` | 5.143 |
| imo_1970_p4 | `accepted` | 6.281 |
| imo_1970_p5 | `accepted` | 7.072 |
| imo_1970_p6 | `accepted` | 7.239 |
| imo_1971_p2 | `accepted` | 10.772 |
| imo_1971_p3 | `accepted` | 5.941 |
| imo_1971_p4 | `accepted` | 7.469 |
| imo_1971_p5 | `accepted` | 6.882 |
| imo_1972_p1 | `accepted` | 7.051 |
| imo_1972_p2 | `accepted` | 7.032 |
| imo_1972_p3 | `accepted` | 6.068 |
| imo_1972_p4 | `accepted` | 11.269 |
| imo_1972_p5 | `accepted` | 5.651 |
| imo_1972_p6 | `accepted` | 9.459 |
| imo_1973_p1 | `accepted` | 11.978 |
| imo_1973_p2 | `accepted` | 18.865 |
| imo_1973_p3 | `accepted` | 10.153 |
| imo_1973_p4 | `accepted` | 6.597 |
| imo_1973_p5 | `accepted` | 7.288 |
| imo_1973_p6 | `accepted` | 10.24 |
| imo_1974_p1 | `accepted` | 16.048 |
| imo_1974_p2 | `accepted` | 49.686 |
| imo_1974_p3 | `accepted` | 9.83 |
| imo_1974_p4 | `accepted` | 23.733 |
| imo_1974_p5 | `accepted` | 13.024 |
| imo_1974_p6 | `accepted` | 7.815 |
| imo_1975_p1 | `accepted` | 7.278 |
| imo_1975_p2 | `accepted` | 6.513 |
| imo_1975_p3 | `accepted` | 11.478 |
| imo_1975_p4 | `accepted` | 8.365 |
| imo_1975_p5 | `accepted` | 7.787 |
| imo_1975_p6 | `accepted` | 10.269 |
| imo_1976_p1 | `accepted` | 24.711 |
| imo_1976_p2 | `accepted` | 13.073 |
| imo_1976_p3 | `timeout` | 600.733 |
| imo_1976_p4 | `accepted` | 7.635 |
| imo_1976_p5 | `accepted` | 8.675 |
| imo_1976_p6 | `accepted` | 6.796 |
| imo_1977_p1 | `accepted` | 8.363 |
| imo_1977_p2 | `accepted` | 13.441 |
| imo_1977_p3 | `accepted` | 9.534 |
| imo_1977_p4 | `compile_error` | 11.834 |
| imo_1977_p5 | `accepted` | 8.711 |
| imo_1977_p6 | `accepted` | 6.886 |
| imo_1978_p1 | `accepted` | 5.478 |
| imo_1978_p2 | `accepted` | 8.11 |
| imo_1978_p3 | `accepted` | 6.334 |
| imo_1978_p5 | `accepted` | 6.23 |
| imo_1978_p6 | `accepted` | 7.665 |
| imo_1979_p1 | `accepted` | 9.311 |
| imo_1979_p2 | `accepted` | 10.341 |
| imo_1979_p3 | `accepted` | 7.989 |
| imo_1979_p4 | `accepted` | 30.891 |
| imo_1979_p5 | `accepted` | 13.183 |
| imo_1979_p6 | `compile_error` | 8.079 |
| imo_1981_p1 | `accepted` | 13.096 |
| imo_1981_p2 | `accepted` | 6.285 |
| imo_1981_p3 | `accepted` | 10.433 |
| imo_1981_p4 | `accepted` | 8.246 |
| imo_1981_p5 | `accepted` | 14.959 |
| imo_1981_p6 | `accepted` | 5.412 |
| imo_1982_p1 | `accepted` | 7.04 |
| imo_1982_p2 | `compile_error` | 6.735 |
| imo_1982_p3 | `accepted` | 8.631 |
| imo_1982_p4 | `accepted` | 7.108 |
| imo_1982_p5 | `accepted` | 6.72 |
| imo_1982_p6 | `accepted` | 7.57 |
| imo_1983_p1 | `accepted` | 6.975 |
| imo_1983_p2 | `accepted` | 31.45 |
| imo_1983_p3 | `accepted` | 12.787 |
| imo_1983_p4 | `accepted` | 10.095 |
| imo_1983_p5 | `accepted` | 8.205 |
| imo_1983_p6 | `accepted` | 7.543 |
| imo_1984_p1 | `accepted` | 10.599 |
| imo_1984_p2 | `accepted` | 7.703 |
| imo_1984_p3 | `accepted` | 5.516 |
| imo_1984_p4 | `accepted` | 6.808 |
| imo_1984_p5 | `accepted` | 8.115 |
| imo_1984_p6 | `accepted` | 6.217 |
| imo_1985_p1 | `accepted` | 7.976 |
| imo_1985_p2 | `accepted` | 7.937 |
| imo_1985_p4 | `accepted` | 6.926 |
| imo_1985_p5 | `accepted` | 6.077 |
| imo_1985_p6 | `accepted` | 8.84 |
| imo_1986_p1 | `accepted` | 8.254 |
| imo_1986_p2 | `accepted` | 5.794 |
| imo_1986_p3 | `accepted` | 7.523 |
| imo_1986_p4 | `accepted` | 7.479 |
| imo_1986_p5 | `accepted` | 6.744 |
| imo_1986_p6 | `accepted` | 6.096 |
| imo_1987_p1 | `accepted` | 7.717 |
| imo_1987_p2 | `accepted` | 6.99 |
| imo_1987_p3 | `accepted` | 6.248 |
| imo_1987_p4 | `accepted` | 5.964 |
| imo_1987_p5 | `accepted` | 6.622 |
| imo_1987_p6 | `accepted` | 10.181 |
| imo_1988_p1 | `accepted` | 22.207 |
| imo_1988_p3 | `accepted` | 10.288 |
| imo_1988_p4 | `accepted` | 5.851 |
| imo_1988_p6 | `accepted` | 9.244 |
| imo_1989_p2 | `accepted` | 7.673 |
| imo_1989_p3 | `accepted` | 7.718 |
| imo_1989_p4 | `accepted` | 13.118 |
| imo_1989_p5 | `accepted` | 5.737 |
| imo_1989_p6 | `accepted` | 7.431 |
| imo_1990_p1 | `accepted` | 6.368 |
| imo_1990_p2 | `accepted` | 8.243 |
| imo_1990_p3 | `compile_error` | 8.741 |
| imo_1990_p4 | `accepted` | 8.123 |
| imo_1990_p5 | `accepted` | 8.242 |
| imo_1990_p6 | `accepted` | 6.048 |
| imo_1991_p1 | `accepted` | 9.769 |
| imo_1991_p2 | `accepted` | 8.582 |
| imo_1991_p3 | `accepted` | 11.238 |
| imo_1991_p4 | `accepted` | 6.237 |
| imo_1991_p5 | `accepted` | 8.687 |
| imo_1991_p6 | `accepted` | 11.02 |
| imo_1992_p1 | `accepted` | 16.88 |
| imo_1992_p2 | `accepted` | 7.411 |
| imo_1992_p3 | `accepted` | 7.397 |
| imo_1992_p4 | `accepted` | 10.238 |
| imo_1992_p5 | `accepted` | 8.199 |
| imo_1992_p6 | `accepted` | 8.153 |
| imo_1993_p1 | `accepted` | 8.51 |
| imo_1993_p2 | `accepted` | 7.089 |
| imo_1993_p3 | `accepted` | 6.704 |
| imo_1993_p4 | `accepted` | 7.058 |
| imo_1993_p5 | `accepted` | 4.361 |
| imo_1993_p6 | `accepted` | 7.266 |
| imo_1994_p1 | `accepted` | 2.911 |
| imo_1994_p2 | `accepted` | 8.736 |
| imo_1994_p3 | `accepted` | 7.939 |
| imo_1994_p4 | `accepted` | 14.623 |
| imo_1994_p5 | `accepted` | 7.051 |
| imo_1994_p6 | `accepted` | 3.612 |
| imo_1995_p1 | `accepted` | 7.063 |
| imo_1995_p2 | `accepted` | 6.056 |
| imo_1995_p3 | `accepted` | 8.944 |
| imo_1995_p4 | `accepted` | 8.059 |
| imo_1995_p5 | `accepted` | 15.136 |
| imo_1995_p6 | `compile_error` | 8.003 |
| imo_1996_p1 | `compile_error` | 10.027 |
| imo_1996_p2 | `accepted` | 8.494 |
| imo_1996_p3 | `accepted` | 7.372 |
| imo_1996_p4 | `accepted` | 7.171 |
| imo_1996_p5 | `accepted` | 9.593 |
| imo_1996_p6 | `accepted` | 15.931 |
| imo_1997_p1 | `accepted` | 6.969 |
| imo_1997_p2 | `accepted` | 6.588 |
| imo_1997_p3 | `accepted` | 7.402 |
| imo_1997_p4 | `accepted` | 7.215 |
| imo_1997_p6 | `accepted` | 8.499 |
| imo_1998_p1 | `accepted` | 10.463 |
| imo_1998_p2 | `accepted` | 10.873 |
| imo_1998_p3 | `compile_error` | 8.85 |
| imo_1998_p4 | `accepted` | 11.495 |
| imo_1998_p5 | `accepted` | 20.759 |
| imo_1998_p6 | `accepted` | 11.447 |
| imo_1999_p1 | `accepted` | 12.032 |
| imo_1999_p2 | `accepted` | 11.207 |
| imo_1999_p3 | `accepted` | 14.063 |
| imo_1999_p4 | `compile_error` | 8.055 |
| imo_1999_p5 | `accepted` | 10.803 |
| imo_1999_p6 | `accepted` | 6.933 |
| imo_2000_p1 | `accepted` | 7.729 |
| imo_2000_p2 | `compile_error` | 5.666 |
| imo_2000_p3 | `accepted` | 11.703 |
| imo_2000_p4 | `accepted` | 14.242 |
| imo_2000_p5 | `accepted` | 9.474 |
| imo_2001_p1 | `accepted` | 6.801 |
| imo_2001_p2 | `accepted` | 5.082 |
| imo_2001_p3 | `accepted` | 4.573 |
| imo_2001_p4 | `accepted` | 3.37 |
| imo_2001_p5 | `accepted` | 19.264 |
| imo_2001_p6 | `accepted` | 8.144 |
| imo_2002_p1 | `accepted` | 6.658 |
| imo_2002_p2 | `accepted` | 9.548 |
| imo_2002_p4 | `accepted` | 7.624 |
| imo_2002_p5 | `accepted` | 6.803 |
| imo_2002_p6 | `accepted` | 7.932 |
| imo_2003_p1 | `accepted` | 4.498 |
| imo_2003_p2 | `accepted` | 11.716 |
| imo_2003_p3 | `accepted` | 14.578 |
| imo_2003_p5 | `accepted` | 7.452 |
| imo_2003_p6 | `accepted` | 6.267 |
| imo_2004_p1 | `accepted` | 17.055 |
| imo_2004_p2 | `accepted` | 8.272 |
| imo_2004_p4 | `compile_error` | 23.192 |
| imo_2004_p5 | `compile_error` | 41.016 |
| imo_2004_p6 | `accepted` | 5.781 |
| imo_2005_p1 | `accepted` | 10.37 |
| imo_2005_p2 | `accepted` | 6.131 |
| imo_2005_p3 | `accepted` | 8.951 |
| imo_2005_p4 | `compile_error` | 6.4 |
| imo_2006_p1 | `accepted` | 8.246 |
| imo_2006_p2 | `accepted` | 6.386 |
| imo_2006_p3 | `accepted` | 11.94 |
| imo_2006_p4 | `accepted` | 16.344 |
| imo_2006_p5 | `accepted` | 7.429 |
| imo_2007_p1 | `accepted` | 7.818 |
| imo_2007_p2 | `accepted` | 10.749 |
| imo_2007_p3 | `accepted` | 9.629 |
| imo_2007_p4 | `accepted` | 7.237 |
| imo_2007_p5 | `accepted` | 11.21 |
| imo_2007_p6 | `accepted` | 6.815 |
| imo_2008_p1 | `accepted` | 9.064 |
| imo_2008_p2 | `accepted` | 9.799 |
| imo_2008_p3 | `compile_error` | 8.798 |
| imo_2008_p4 | `accepted` | 11.907 |
| imo_2008_p5 | `compile_error` | 9.16 |
| imo_2009_p1 | `accepted` | 6.463 |
| imo_2009_p2 | `accepted` | 8.12 |
| imo_2009_p3 | `accepted` | 7.505 |
| imo_2009_p4 | `accepted` | 5.447 |
| imo_2009_p5 | `accepted` | 6.519 |
| imo_2009_p6 | `accepted` | 8.744 |
| imo_2010_p1 | `accepted` | 8.085 |
| imo_2010_p2 | `accepted` | 6.319 |
| imo_2010_p3 | `compile_error` | 7.614 |
| imo_2010_p4 | `accepted` | 6.871 |
| imo_2010_p5 | `compile_error` | 10.464 |
| imo_2010_p6 | `accepted` | 5.801 |
| imo_2011_p1 | `accepted` | 7.999 |
| imo_2011_p2 | `accepted` | 6.211 |
| imo_2011_p3 | `accepted` | 8.587 |
| imo_2011_p4 | `accepted` | 6.592 |
| imo_2011_p5 | `accepted` | 7.294 |
| imo_2011_p6 | `accepted` | 19.256 |
| imo_2012_p1 | `accepted` | 7.861 |
| imo_2012_p2 | `accepted` | 7.256 |
| imo_2012_p3 | `accepted` | 7.515 |
| imo_2012_p4 | `accepted` | 7.887 |
| imo_2012_p5 | `accepted` | 7.196 |
| imo_2013_p1 | `accepted` | 6.336 |
| imo_2013_p2 | `accepted` | 6.92 |
| imo_2013_p3 | `accepted` | 6.57 |
| imo_2013_p4 | `accepted` | 7.695 |
| imo_2014_p1 | `accepted` | 6.537 |
| imo_2014_p2 | `accepted` | 7.46 |
| imo_2014_p3 | `accepted` | 7.144 |
| imo_2014_p4 | `accepted` | 7.554 |
| imo_2014_p5 | `accepted` | 6.471 |
| imo_2014_p6 | `accepted` | 7.609 |
| imo_2015_p1 | `accepted` | 6.989 |
| imo_2015_p2 | `accepted` | 7.304 |
| imo_2015_p3 | `accepted` | 8.761 |
| imo_2015_p4 | `accepted` | 7.717 |
| imo_2015_p5 | `accepted` | 7.466 |
| imo_2015_p6 | `accepted` | 7.245 |
| imo_2016_p1 | `accepted` | 7.571 |
| imo_2016_p2 | `accepted` | 6.521 |
| imo_2016_p3 | `accepted` | 6.615 |
| imo_2016_p4 | `accepted` | 6.264 |
| imo_2016_p6 | `accepted` | 6.816 |
| imo_2017_p1 | `compile_error` | 6.67 |
| imo_2017_p2 | `accepted` | 7.583 |
| imo_2017_p3 | `accepted` | 7.892 |
| imo_2017_p4 | `accepted` | 6.285 |
| imo_2017_p6 | `compile_error` | 8.926 |
| imo_2018_p1 | `compile_error` | 38.256 |
| imo_2018_p2 | `accepted` | 9.386 |
| imo_2018_p3 | `accepted` | 8.991 |
| imo_2018_p5 | `accepted` | 7.704 |
| imo_2018_p6 | `accepted` | 6.672 |
| imo_2019_p1 | `accepted` | 7.412 |
| imo_2019_p2 | `accepted` | 5.872 |
| imo_2019_p3 | `accepted` | 6.92 |
| imo_2019_p4 | `accepted` | 7.685 |
| imo_2019_p5 | `accepted` | 7.784 |
| imo_2019_p6 | `accepted` | 5.654 |
| imo_2020_p1 | `accepted` | 7.088 |
| imo_2020_p2 | `accepted` | 9.367 |
| imo_2020_p5 | `accepted` | 5.967 |
| imo_2020_p6 | `accepted` | 5.789 |
| imo_2021_p1 | `accepted` | 6.354 |
| imo_2021_p2 | `accepted` | 6.416 |
| imo_2021_p3 | `accepted` | 7.13 |
| imo_2021_p4 | `accepted` | 6.79 |
| imo_2021_p5 | `accepted` | 6.096 |
| imo_2022_p1 | `accepted` | 5.957 |
| imo_2022_p2 | `accepted` | 8.218 |
| imo_2022_p3 | `accepted` | 6.4 |
| imo_2022_p6 | `accepted` | 5.877 |
| imo_2023_p1 | `accepted` | 6.517 |
| imo_2023_p2 | `accepted` | 7.383 |
| imo_2023_p3 | `accepted` | 6.914 |
| imo_2023_p4 | `accepted` | 6.15 |
| imo_2024_p1 | `accepted` | 7.661 |
| imo_2024_p2 | `accepted` | 9.943 |
| imo_2024_p4 | `accepted` | 6.74 |
| imo_2024_p5 | `accepted` | 6.205 |
| imo_2025_p1 | `accepted` | 7.145 |
| imo_2025_p4 | `accepted` | 6.405 |
| imo_2025_p5 | `accepted` | 7.631 |
| imo_2026_p1 | `accepted` | 6.733 |
| imo_2026_p2 | `accepted` | 6.282 |
| imo_2026_p3 | `accepted` | 6.587 |
| imo_2026_p4 | `accepted` | 7.873 |
| imo_2026_p5 | `accepted` | 7.381 |
| imo_2026_p6 | `accepted` | 7.829 |
