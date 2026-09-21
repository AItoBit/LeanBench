# Importacion IMO

Archivos analizados: **358**

| Categoria | Significado | Archivos |
| --------- | ----------- | -------- |
| A | Enunciado limpio: se importa tal cual | 66 |
| B | Necesita definiciones previas: se importa con ellas | 7 |
| C | Lemas auxiliares: pendiente del modo archivo completo | 278 |
| X | Excluido (ver motivo) | 7 |

Importados a `imports/imo/`: **73**. De ellos, 31 tienen la marca `core_like`: revisa con cuidado si formalizan el problema completo o solo una parte.

Ninguno entra en el benchmark hasta que lo revises y lo promuevas:

```
python scripts/promote.py imo_1959_p1 --split dev
```

## Excluidos (X)

| Problema | Motivo |
| -------- | ------ |
| imo_1971_p1 | declara axiom; no hay teorema principal |
| imo_1971_p6 | declara axiom |
| imo_1989_p1 | usa native_decide (la auditoria lo rechaza) |
| imo_1997_p5 | declara axiom |
| imo_2003_p4 | usa sorry/admit |
| imo_2017_p5 | no hay teorema principal |
| imo_2018_p4 | usa native_decide (la auditoria lo rechaza) |

## Importados (A y B)

| Problema | Cat. | Tema (estimado) | Marcas |
| -------- | ---- | --------------- | ------ |
| imo_1959_p1 | A | number_theory |  |
| imo_1964_p2 | A | algebra |  |
| imo_1965_p2 | A | algebra |  |
| imo_1965_p4 | A | algebra |  |
| imo_1966_p1 | A | algebra |  |
| imo_1966_p2 | A | algebra |  |
| imo_1966_p5 | A | algebra |  |
| imo_1966_p6 | A | algebra |  |
| imo_1967_p1 | A | algebra |  |
| imo_1967_p2 | A | algebra |  |
| imo_1967_p4 | A | algebra | core_like |
| imo_1968_p1 | A | algebra | core_like |
| imo_1968_p2 | A | algebra |  |
| imo_1968_p4 | A | algebra |  |
| imo_1968_p6 | A | algebra |  |
| imo_1969_p1 | A | number_theory |  |
| imo_1969_p2 | A | algebra | core_like |
| imo_1969_p3 | A | algebra |  |
| imo_1970_p2 | A | algebra | core_like |
| imo_1970_p3 | A | algebra |  |
| imo_1970_p5 | A | algebra | core_like |
| imo_1970_p6 | A | algebra | core_like |
| imo_1971_p2 | B | algebra |  |
| imo_1972_p5 | A | algebra |  |
| imo_1973_p3 | A | algebra |  |
| imo_1973_p5 | A | algebra |  |
| imo_1975_p2 | A | algebra |  |
| imo_1977_p1 | A | algebra |  |
| imo_1977_p2 | A | algebra | core_like |
| imo_1977_p6 | A | algebra | core_like |
| imo_1978_p3 | A | algebra | core_like |
| imo_1982_p1 | A | algebra | core_like |
| imo_1982_p5 | A | algebra |  |
| imo_1983_p5 | A | algebra |  |
| imo_1983_p6 | A | geometry |  |
| imo_1984_p3 | A | algebra | core_like, usa variable |
| imo_1984_p4 | A | algebra | core_like |
| imo_1984_p6 | A | algebra | core_like |
| imo_1985_p1 | A | algebra | core_like |
| imo_1985_p2 | A | number_theory | core_like |
| imo_1985_p4 | A | algebra | core_like |
| imo_1985_p5 | A | algebra | core_like |
| imo_1986_p1 | A | algebra | core_like |
| imo_1986_p2 | A | algebra | core_like |
| imo_1986_p3 | B | algebra | core_like |
| imo_1986_p4 | A | algebra | core_like |
| imo_1986_p5 | A | algebra | core_like |
| imo_1986_p6 | A | algebra | core_like |
| imo_1987_p2 | A | algebra | core_like |
| imo_1987_p3 | A | algebra | core_like |
| imo_1987_p4 | A | algebra |  |
| imo_1987_p6 | A | number_theory |  |
| imo_1988_p3 | A | algebra |  |
| imo_1988_p4 | A | algebra | core_like |
| imo_1990_p6 | A | algebra | core_like |
| imo_1991_p4 | B | algebra |  |
| imo_1991_p5 | B | algebra |  |
| imo_1991_p6 | A | algebra |  |
| imo_1992_p1 | A | number_theory |  |
| imo_1992_p2 | A | algebra |  |
| imo_1994_p1 | A | algebra |  |
| imo_1994_p5 | B | algebra |  |
| imo_1995_p1 | A | algebra |  |
| imo_1996_p3 | A | number_theory | core_like |
| imo_1996_p5 | A | algebra | core_like |
| imo_1997_p2 | A | algebra | core_like |
| imo_1999_p6 | A | algebra |  |
| imo_2000_p1 | A | geometry |  |
| imo_2003_p3 | A | algebra |  |
| imo_2005_p4 | A | number_theory |  |
| imo_2007_p4 | A | algebra | core_like |
| imo_2010_p1 | B | algebra |  |
| imo_2011_p3 | B | algebra |  |

## Pendientes (C)

| Problema | Lemas auxiliares |
| -------- | ---------------- |
| imo_1959_p2 | 17 |
| imo_1959_p3 | 1 |
| imo_1959_p4 | 1 |
| imo_1960_p1 | 1 |
| imo_1960_p2 | 1 |
| imo_1961_p1 | 4 |
| imo_1961_p3 | 1 |
| imo_1962_p1 | 6 |
| imo_1962_p2 | 1 |
| imo_1963_p1 | 2 |
| imo_1963_p4 | 1 |
| imo_1963_p5 | 2 |
| imo_1964_p1 | 3 |
| imo_1964_p4 | 3 |
| imo_1965_p1 | 10 |
| imo_1965_p3 | 5 |
| imo_1965_p5 | 16 |
| imo_1965_p6 | 4 |
| imo_1966_p3 | 4 |
| imo_1966_p4 | 1 |
| imo_1967_p3 | 3 |
| imo_1967_p5 | 2 |
| imo_1967_p6 | 1 |
| imo_1968_p3 | 3 |
| imo_1968_p5 | 15 |
| imo_1969_p4 | 1 |
| imo_1969_p5 | 23 |
| imo_1969_p6 | 7 |
| imo_1970_p1 | 1 |
| imo_1970_p4 | 3 |
| imo_1971_p3 | 14 |
| imo_1971_p4 | 3 |
| imo_1971_p5 | 8 |
| imo_1972_p1 | 2 |
| imo_1972_p2 | 5 |
| imo_1972_p3 | 4 |
| imo_1972_p4 | 2 |
| imo_1972_p6 | 4 |
| imo_1973_p1 | 1 |
| imo_1973_p2 | 1 |
| imo_1973_p4 | 5 |
| imo_1973_p6 | 14 |
| imo_1974_p1 | 3 |
| imo_1974_p2 | 5 |
| imo_1974_p3 | 6 |
| imo_1974_p4 | 20 |
| imo_1974_p5 | 5 |
| imo_1974_p6 | 13 |
| imo_1975_p1 | 2 |
| imo_1975_p3 | 22 |
| imo_1975_p4 | 5 |
| imo_1975_p5 | 15 |
| imo_1975_p6 | 23 |
| imo_1976_p1 | 4 |
| imo_1976_p2 | 17 |
| imo_1976_p3 | 17 |
| imo_1976_p4 | 6 |
| imo_1976_p5 | 4 |
| imo_1976_p6 | 11 |
| imo_1977_p3 | 2 |
| imo_1977_p4 | 1 |
| imo_1977_p5 | 5 |
| imo_1978_p1 | 3 |
| imo_1978_p2 | 2 |
| imo_1978_p5 | 3 |
| imo_1978_p6 | 1 |
| imo_1979_p1 | 7 |
| imo_1979_p2 | 5 |
| imo_1979_p3 | 4 |
| imo_1979_p4 | 16 |
| imo_1979_p5 | 2 |
| imo_1979_p6 | 24 |
| imo_1981_p1 | 16 |
| imo_1981_p2 | 4 |
| imo_1981_p3 | 2 |
| imo_1981_p4 | 5 |
| imo_1981_p5 | 17 |
| imo_1981_p6 | 4 |
| imo_1982_p2 | 2 |
| imo_1982_p3 | 2 |
| imo_1982_p4 | 1 |
| imo_1982_p6 | 3 |
| imo_1983_p1 | 1 |
| imo_1983_p2 | 10 |
| imo_1983_p3 | 2 |
| imo_1983_p4 | 16 |
| imo_1984_p1 | 4 |
| imo_1984_p2 | 1 |
| imo_1984_p5 | 1 |
| imo_1985_p6 | 19 |
| imo_1987_p1 | 1 |
| imo_1987_p5 | 3 |
| imo_1988_p1 | 21 |
| imo_1988_p2 | 19 |
| imo_1988_p5 | 5 |
| imo_1988_p6 | 2 |
| imo_1989_p2 | 3 |
| imo_1989_p3 | 1 |
| imo_1989_p4 | 2 |
| imo_1989_p5 | 1 |
| imo_1989_p6 | 9 |
| imo_1990_p1 | 2 |
| imo_1990_p2 | 20 |
| imo_1990_p3 | 7 |
| imo_1990_p4 | 18 |
| imo_1990_p5 | 5 |
| imo_1991_p1 | 3 |
| imo_1991_p2 | 10 |
| imo_1991_p3 | 13 |
| imo_1992_p3 | 5 |
| imo_1992_p4 | 2 |
| imo_1992_p5 | 1 |
| imo_1992_p6 | 3 |
| imo_1993_p1 | 8 |
| imo_1993_p2 | 2 |
| imo_1993_p3 | 5 |
| imo_1993_p4 | 1 |
| imo_1993_p5 | 5 |
| imo_1993_p6 | 2 |
| imo_1994_p2 | 2 |
| imo_1994_p3 | 19 |
| imo_1994_p4 | 1 |
| imo_1994_p6 | 2 |
| imo_1995_p2 | 2 |
| imo_1995_p3 | 10 |
| imo_1995_p4 | 6 |
| imo_1995_p5 | 17 |
| imo_1995_p6 | 34 |
| imo_1996_p1 | 11 |
| imo_1996_p2 | 2 |
| imo_1996_p4 | 2 |
| imo_1996_p6 | 1 |
| imo_1997_p1 | 1 |
| imo_1997_p3 | 10 |
| imo_1997_p4 | 10 |
| imo_1997_p6 | 24 |
| imo_1998_p1 | 1 |
| imo_1998_p2 | 3 |
| imo_1998_p3 | 8 |
| imo_1998_p4 | 1 |
| imo_1998_p5 | 17 |
| imo_1998_p6 | 24 |
| imo_1999_p1 | 20 |
| imo_1999_p2 | 14 |
| imo_1999_p3 | 22 |
| imo_1999_p4 | 2 |
| imo_1999_p5 | 5 |
| imo_2000_p2 | 1 |
| imo_2000_p3 | 20 |
| imo_2000_p4 | 8 |
| imo_2000_p5 | 10 |
| imo_2001_p1 | 3 |
| imo_2001_p2 | 2 |
| imo_2001_p3 | 3 |
| imo_2001_p4 | 4 |
| imo_2001_p5 | 1 |
| imo_2001_p6 | 2 |
| imo_2002_p1 | 9 |
| imo_2002_p2 | 8 |
| imo_2002_p3 | 9 |
| imo_2002_p4 | 2 |
| imo_2002_p5 | 1 |
| imo_2002_p6 | 4 |
| imo_2003_p1 | 5 |
| imo_2003_p2 | 1 |
| imo_2003_p5 | 9 |
| imo_2003_p6 | 2 |
| imo_2004_p1 | 1 |
| imo_2004_p2 | 2 |
| imo_2004_p4 | 2 |
| imo_2004_p5 | 1 |
| imo_2004_p6 | 2 |
| imo_2005_p1 | 1 |
| imo_2005_p2 | 1 |
| imo_2005_p3 | 3 |
| imo_2006_p1 | 2 |
| imo_2006_p2 | 3 |
| imo_2006_p3 | 3 |
| imo_2006_p4 | 1 |
| imo_2006_p5 | 10 |
| imo_2007_p1 | 9 |
| imo_2007_p2 | 6 |
| imo_2007_p3 | 7 |
| imo_2007_p5 | 4 |
| imo_2007_p6 | 1 |
| imo_2008_p1 | 1 |
| imo_2008_p2 | 3 |
| imo_2008_p3 | 1 |
| imo_2008_p4 | 3 |
| imo_2008_p5 | 20 |
| imo_2009_p1 | 4 |
| imo_2009_p2 | 2 |
| imo_2009_p3 | 5 |
| imo_2009_p4 | 3 |
| imo_2009_p5 | 7 |
| imo_2009_p6 | 7 |
| imo_2010_p2 | 6 |
| imo_2010_p3 | 2 |
| imo_2010_p4 | 3 |
| imo_2010_p5 | 12 |
| imo_2010_p6 | 6 |
| imo_2011_p1 | 20 |
| imo_2011_p2 | 5 |
| imo_2011_p4 | 9 |
| imo_2011_p5 | 1 |
| imo_2011_p6 | 4 |
| imo_2012_p1 | 7 |
| imo_2012_p2 | 6 |
| imo_2012_p3 | 19 |
| imo_2012_p4 | 14 |
| imo_2012_p5 | 7 |
| imo_2013_p1 | 6 |
| imo_2013_p2 | 12 |
| imo_2013_p3 | 10 |
| imo_2013_p4 | 11 |
| imo_2014_p1 | 12 |
| imo_2014_p2 | 12 |
| imo_2014_p3 | 5 |
| imo_2014_p4 | 8 |
| imo_2014_p5 | 12 |
| imo_2014_p6 | 9 |
| imo_2015_p1 | 9 |
| imo_2015_p2 | 32 |
| imo_2015_p3 | 6 |
| imo_2015_p4 | 9 |
| imo_2015_p5 | 17 |
| imo_2015_p6 | 6 |
| imo_2016_p1 | 13 |
| imo_2016_p2 | 9 |
| imo_2016_p3 | 9 |
| imo_2016_p4 | 16 |
| imo_2016_p6 | 14 |
| imo_2017_p1 | 23 |
| imo_2017_p2 | 16 |
| imo_2017_p3 | 16 |
| imo_2017_p4 | 10 |
| imo_2017_p6 | 14 |
| imo_2018_p1 | 3 |
| imo_2018_p2 | 15 |
| imo_2018_p3 | 24 |
| imo_2018_p5 | 11 |
| imo_2018_p6 | 9 |
| imo_2019_p1 | 12 |
| imo_2019_p2 | 8 |
| imo_2019_p3 | 12 |
| imo_2019_p4 | 28 |
| imo_2019_p5 | 13 |
| imo_2019_p6 | 13 |
| imo_2020_p1 | 10 |
| imo_2020_p2 | 16 |
| imo_2020_p5 | 14 |
| imo_2020_p6 | 6 |
| imo_2021_p1 | 2 |
| imo_2021_p2 | 12 |
| imo_2021_p3 | 8 |
| imo_2021_p4 | 10 |
| imo_2021_p5 | 15 |
| imo_2022_p1 | 12 |
| imo_2022_p2 | 7 |
| imo_2022_p3 | 10 |
| imo_2022_p6 | 6 |
| imo_2023_p1 | 15 |
| imo_2023_p2 | 11 |
| imo_2023_p3 | 11 |
| imo_2023_p4 | 10 |
| imo_2024_p1 | 3 |
| imo_2024_p2 | 10 |
| imo_2024_p4 | 11 |
| imo_2024_p5 | 5 |
| imo_2025_p1 | 11 |
| imo_2025_p4 | 15 |
| imo_2025_p5 | 18 |
| imo_2026_p1 | 9 |
| imo_2026_p2 | 11 |
| imo_2026_p3 | 11 |
| imo_2026_p4 | 14 |
| imo_2026_p5 | 12 |
| imo_2026_p6 | 9 |
