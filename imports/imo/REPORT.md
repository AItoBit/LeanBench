# Importacion IMO

Archivos analizados: **358**

| Categoria | Significado | Archivos |
| --------- | ----------- | -------- |
| A | Enunciado limpio: se importa tal cual | 66 |
| B | Necesita definiciones previas: se importa con ellas | 7 |
| C | Usa lemas auxiliares propios: se importan como parte de la referencia | 276 |
| X | Excluido (ver motivo) | 9 |

Importados a `imports/imo/`: **349**. De ellos, 145 tienen la marca `core_like`: revisa con cuidado si formalizan el problema completo o solo una parte.

Ninguno entra en el benchmark hasta que lo revises y lo promuevas:

```
python scripts/promote.py imo_1959_p1 --split dev
```

## Excluidos (X)

| Problema | Motivo |
| -------- | ------ |
| imo_1971_p1 | declara axiom; no hay teorema principal |
| imo_1971_p6 | declara axiom |
| imo_1988_p2 | el evaluador rechazaria los lemas: en los lemas auxiliares solo se admiten theorem/lemma (linea 26: 'include') |
| imo_1989_p1 | usa native_decide (la auditoria lo rechaza) |
| imo_1997_p5 | declara axiom |
| imo_2002_p3 | el evaluador rechazaria los lemas: en los lemas auxiliares solo se admiten theorem/lemma (linea 4: 'include') |
| imo_2003_p4 | usa sorry/admit |
| imo_2017_p5 | no hay teorema principal |
| imo_2018_p4 | usa native_decide (la auditoria lo rechaza) |

## Importados (A, B y C)

| Problema | Cat. | Tema (estimado) | Marcas |
| -------- | ---- | --------------- | ------ |
| imo_1959_p1 | A | number_theory |  |
| imo_1959_p2 | C | algebra | usa variable |
| imo_1959_p3 | C | algebra |  |
| imo_1959_p4 | C | algebra |  |
| imo_1960_p1 | C | number_theory |  |
| imo_1960_p2 | C | algebra |  |
| imo_1961_p1 | C | algebra | core_like |
| imo_1961_p3 | C | algebra |  |
| imo_1962_p1 | C | number_theory |  |
| imo_1962_p2 | C | algebra | core_like |
| imo_1963_p1 | C | algebra |  |
| imo_1963_p4 | C | algebra |  |
| imo_1963_p5 | C | algebra |  |
| imo_1964_p1 | C | number_theory |  |
| imo_1964_p2 | A | algebra |  |
| imo_1964_p4 | C | algebra |  |
| imo_1965_p1 | C | algebra |  |
| imo_1965_p2 | A | algebra |  |
| imo_1965_p3 | C | algebra |  |
| imo_1965_p4 | A | algebra |  |
| imo_1965_p5 | C | algebra |  |
| imo_1965_p6 | C | geometry | core_like |
| imo_1966_p1 | A | algebra |  |
| imo_1966_p2 | A | algebra |  |
| imo_1966_p3 | C | geometry | declaraciones despues del teorema: ['exists_regular_tetrahedron_with_circumcenter'] |
| imo_1966_p4 | C | algebra |  |
| imo_1966_p5 | A | algebra |  |
| imo_1966_p6 | A | algebra |  |
| imo_1967_p1 | A | algebra |  |
| imo_1967_p2 | A | algebra |  |
| imo_1967_p3 | C | number_theory | core_like |
| imo_1967_p4 | A | algebra | core_like |
| imo_1967_p5 | C | algebra | core_like |
| imo_1967_p6 | C | algebra | core_like |
| imo_1968_p1 | A | algebra | core_like |
| imo_1968_p2 | A | algebra |  |
| imo_1968_p3 | C | algebra | core_like |
| imo_1968_p4 | A | algebra |  |
| imo_1968_p5 | C | algebra | declaraciones despues del teorema: ['square_inConvexPosition', 'not_inConvexPosition_triangle_with_interior_point'] |
| imo_1968_p6 | A | algebra |  |
| imo_1969_p1 | A | number_theory |  |
| imo_1969_p2 | A | algebra | core_like |
| imo_1969_p3 | A | algebra |  |
| imo_1969_p4 | C | algebra | core_like |
| imo_1969_p5 | C | algebra |  |
| imo_1969_p6 | C | algebra | core_like |
| imo_1970_p1 | C | algebra |  |
| imo_1970_p2 | A | algebra | core_like |
| imo_1970_p3 | A | algebra |  |
| imo_1970_p4 | C | algebra | declaraciones despues del teorema: ['answer_set_eq_empty'] |
| imo_1970_p5 | A | algebra | core_like |
| imo_1970_p6 | A | algebra | core_like |
| imo_1971_p2 | B | algebra |  |
| imo_1971_p3 | C | number_theory |  |
| imo_1971_p4 | C | geometry | core_like, usa variable |
| imo_1971_p5 | C | geometry |  |
| imo_1972_p1 | C | algebra |  |
| imo_1972_p2 | C | geometry |  |
| imo_1972_p3 | C | number_theory |  |
| imo_1972_p4 | C | algebra |  |
| imo_1972_p5 | A | algebra |  |
| imo_1972_p6 | C | geometry |  |
| imo_1973_p1 | C | algebra | core_like |
| imo_1973_p2 | C | algebra |  |
| imo_1973_p3 | A | algebra |  |
| imo_1973_p4 | C | algebra | core_like |
| imo_1973_p5 | A | algebra |  |
| imo_1973_p6 | C | algebra |  |
| imo_1974_p1 | C | algebra |  |
| imo_1974_p2 | C | geometry |  |
| imo_1974_p3 | C | number_theory |  |
| imo_1974_p4 | C | algebra |  |
| imo_1974_p5 | C | algebra |  |
| imo_1974_p6 | C | algebra |  |
| imo_1975_p1 | C | combinatorics |  |
| imo_1975_p2 | A | algebra |  |
| imo_1975_p3 | C | geometry | declaraciones despues del teorema: ['exists_config'] |
| imo_1975_p4 | C | algebra |  |
| imo_1975_p5 | C | geometry |  |
| imo_1975_p6 | C | algebra |  |
| imo_1976_p1 | C | geometry |  |
| imo_1976_p2 | C | algebra |  |
| imo_1976_p3 | C | algebra | core_like |
| imo_1976_p4 | C | algebra |  |
| imo_1976_p5 | C | algebra |  |
| imo_1976_p6 | C | algebra |  |
| imo_1977_p1 | A | algebra |  |
| imo_1977_p2 | A | algebra | core_like |
| imo_1977_p3 | C | algebra |  |
| imo_1977_p4 | C | algebra |  |
| imo_1977_p5 | C | algebra |  |
| imo_1977_p6 | A | algebra | core_like |
| imo_1978_p1 | C | number_theory |  |
| imo_1978_p2 | C | geometry | usa variable |
| imo_1978_p3 | A | algebra | core_like |
| imo_1978_p5 | C | algebra | core_like |
| imo_1978_p6 | C | algebra |  |
| imo_1979_p1 | C | number_theory |  |
| imo_1979_p2 | C | algebra | usa variable, declaraciones despues del teorema: ['exists_admissible_colouring'] |
| imo_1979_p3 | C | geometry |  |
| imo_1979_p4 | C | geometry | core_like, usa variable |
| imo_1979_p5 | C | algebra |  |
| imo_1979_p6 | C | algebra |  |
| imo_1981_p1 | C | geometry | usa variable |
| imo_1981_p2 | C | algebra |  |
| imo_1981_p3 | C | algebra |  |
| imo_1981_p4 | C | algebra |  |
| imo_1981_p5 | C | geometry | declaraciones despues del teorema: ['pt', 'pt_dist', 'pt_dist_eq'] |
| imo_1981_p6 | C | algebra | usa variable |
| imo_1982_p1 | A | algebra | core_like |
| imo_1982_p2 | C | algebra | core_like |
| imo_1982_p3 | C | algebra |  |
| imo_1982_p4 | C | algebra |  |
| imo_1982_p5 | A | algebra |  |
| imo_1982_p6 | C | geometry | core_like, usa variable |
| imo_1983_p1 | C | algebra | core_like |
| imo_1983_p2 | C | geometry | core_like |
| imo_1983_p3 | C | number_theory |  |
| imo_1983_p4 | C | geometry | core_like, usa variable, declaraciones despues del teorema: ['exists_equilateral'] |
| imo_1983_p5 | A | algebra |  |
| imo_1983_p6 | A | geometry |  |
| imo_1984_p1 | C | algebra | usa variable |
| imo_1984_p2 | C | number_theory | core_like |
| imo_1984_p3 | A | algebra | core_like, usa variable |
| imo_1984_p4 | A | algebra | core_like |
| imo_1984_p5 | C | algebra | core_like |
| imo_1984_p6 | A | algebra | core_like |
| imo_1985_p1 | A | algebra | core_like |
| imo_1985_p2 | A | number_theory | core_like |
| imo_1985_p4 | A | algebra | core_like |
| imo_1985_p5 | A | algebra | core_like |
| imo_1985_p6 | C | algebra |  |
| imo_1986_p1 | A | algebra | core_like |
| imo_1986_p2 | A | algebra | core_like |
| imo_1986_p3 | B | algebra | core_like |
| imo_1986_p4 | A | algebra | core_like |
| imo_1986_p5 | A | algebra | core_like |
| imo_1986_p6 | A | algebra | core_like |
| imo_1987_p1 | C | algebra |  |
| imo_1987_p2 | A | algebra | core_like |
| imo_1987_p3 | A | algebra | core_like |
| imo_1987_p4 | A | algebra |  |
| imo_1987_p5 | C | combinatorics |  |
| imo_1987_p6 | A | number_theory |  |
| imo_1988_p1 | C | geometry | usa variable |
| imo_1988_p3 | A | algebra |  |
| imo_1988_p4 | A | algebra | core_like |
| imo_1988_p5 | C | geometry | declaraciones despues del teorema: ['dist_eq_dist_altitude'] |
| imo_1988_p6 | C | number_theory |  |
| imo_1989_p2 | C | algebra | core_like, usa variable |
| imo_1989_p3 | C | geometry |  |
| imo_1989_p4 | C | algebra | core_like, declaraciones despues del teorema: ['sharp_value'] |
| imo_1989_p5 | C | number_theory |  |
| imo_1989_p6 | C | algebra |  |
| imo_1990_p1 | C | geometry | core_like |
| imo_1990_p2 | C | number_theory |  |
| imo_1990_p3 | C | number_theory |  |
| imo_1990_p4 | C | algebra | core_like |
| imo_1990_p5 | C | algebra |  |
| imo_1990_p6 | A | algebra | core_like |
| imo_1991_p1 | C | algebra | core_like |
| imo_1991_p2 | C | number_theory |  |
| imo_1991_p3 | C | algebra | core_like |
| imo_1991_p4 | B | algebra |  |
| imo_1991_p5 | B | algebra |  |
| imo_1991_p6 | A | algebra |  |
| imo_1992_p1 | A | number_theory |  |
| imo_1992_p2 | A | algebra |  |
| imo_1992_p3 | C | algebra |  |
| imo_1992_p4 | C | algebra |  |
| imo_1992_p5 | C | algebra |  |
| imo_1992_p6 | C | algebra |  |
| imo_1993_p1 | C | algebra | core_like |
| imo_1993_p2 | C | algebra | core_like |
| imo_1993_p3 | C | number_theory |  |
| imo_1993_p4 | C | algebra | core_like |
| imo_1993_p5 | C | algebra |  |
| imo_1993_p6 | C | algebra | usa variable |
| imo_1994_p1 | A | algebra |  |
| imo_1994_p2 | C | algebra |  |
| imo_1994_p3 | C | algebra |  |
| imo_1994_p4 | C | number_theory |  |
| imo_1994_p5 | B | algebra |  |
| imo_1994_p6 | C | combinatorics |  |
| imo_1995_p1 | A | algebra |  |
| imo_1995_p2 | C | algebra |  |
| imo_1995_p3 | C | algebra |  |
| imo_1995_p4 | C | algebra |  |
| imo_1995_p5 | C | geometry | core_like |
| imo_1995_p6 | C | number_theory | usa variable |
| imo_1996_p1 | C | algebra |  |
| imo_1996_p2 | C | algebra | core_like, declaraciones despues del teorema: ['ratio_eq', 'divPt', 'feet_eq'] |
| imo_1996_p3 | A | number_theory | core_like |
| imo_1996_p4 | C | algebra |  |
| imo_1996_p5 | A | algebra | core_like |
| imo_1996_p6 | C | algebra | core_like |
| imo_1997_p1 | C | algebra |  |
| imo_1997_p2 | A | algebra | core_like |
| imo_1997_p3 | C | algebra |  |
| imo_1997_p4 | C | algebra |  |
| imo_1997_p6 | C | algebra | core_like |
| imo_1998_p1 | C | algebra | core_like |
| imo_1998_p2 | C | algebra |  |
| imo_1998_p3 | C | algebra |  |
| imo_1998_p4 | C | number_theory |  |
| imo_1998_p5 | C | geometry | usa variable, declaraciones despues del teorema: ['not_collinear_of_cross_ne_zero'] |
| imo_1998_p6 | C | algebra | usa variable |
| imo_1999_p1 | C | algebra | usa variable |
| imo_1999_p2 | C | algebra | usa variable |
| imo_1999_p3 | C | algebra |  |
| imo_1999_p4 | C | number_theory |  |
| imo_1999_p5 | C | algebra | core_like |
| imo_1999_p6 | A | algebra |  |
| imo_2000_p1 | A | geometry |  |
| imo_2000_p2 | C | algebra | core_like |
| imo_2000_p3 | C | algebra | core_like, usa variable |
| imo_2000_p4 | C | algebra |  |
| imo_2000_p5 | C | number_theory |  |
| imo_2001_p1 | C | geometry | usa variable |
| imo_2001_p2 | C | algebra | usa variable |
| imo_2001_p3 | C | algebra | usa variable |
| imo_2001_p4 | C | combinatorics | usa variable |
| imo_2001_p5 | C | geometry | core_like, usa variable |
| imo_2001_p6 | C | number_theory |  |
| imo_2002_p1 | C | algebra | core_like |
| imo_2002_p2 | C | geometry | usa variable |
| imo_2002_p4 | C | algebra | core_like |
| imo_2002_p5 | C | algebra |  |
| imo_2002_p6 | C | geometry | core_like |
| imo_2003_p1 | C | combinatorics |  |
| imo_2003_p2 | C | algebra |  |
| imo_2003_p3 | A | algebra |  |
| imo_2003_p5 | C | algebra |  |
| imo_2003_p6 | C | number_theory |  |
| imo_2004_p1 | C | algebra |  |
| imo_2004_p2 | C | algebra |  |
| imo_2004_p4 | C | algebra | core_like |
| imo_2004_p5 | C | geometry |  |
| imo_2004_p6 | C | number_theory | core_like, declaraciones despues del teorema: ['div_pow_of_le', 'div_pow_of_ge', 'parity_shift'] |
| imo_2005_p1 | C | algebra | core_like |
| imo_2005_p2 | C | algebra |  |
| imo_2005_p3 | C | algebra |  |
| imo_2005_p4 | A | number_theory |  |
| imo_2006_p1 | C | algebra | usa variable |
| imo_2006_p2 | C | algebra | core_like |
| imo_2006_p3 | C | algebra | core_like |
| imo_2006_p4 | C | algebra |  |
| imo_2006_p5 | C | algebra |  |
| imo_2007_p1 | C | algebra | usa variable |
| imo_2007_p2 | C | geometry | core_like, usa variable |
| imo_2007_p3 | C | combinatorics | usa variable |
| imo_2007_p4 | A | algebra | core_like |
| imo_2007_p5 | C | number_theory |  |
| imo_2007_p6 | C | algebra |  |
| imo_2008_p1 | C | algebra |  |
| imo_2008_p2 | C | algebra |  |
| imo_2008_p3 | C | number_theory | core_like |
| imo_2008_p4 | C | algebra |  |
| imo_2008_p5 | C | algebra | core_like |
| imo_2009_p1 | C | number_theory | core_like |
| imo_2009_p2 | C | algebra | core_like |
| imo_2009_p3 | C | algebra | core_like |
| imo_2009_p4 | C | algebra | core_like |
| imo_2009_p5 | C | algebra |  |
| imo_2009_p6 | C | algebra | core_like |
| imo_2010_p1 | B | algebra |  |
| imo_2010_p2 | C | algebra | core_like, usa variable |
| imo_2010_p3 | C | algebra |  |
| imo_2010_p4 | C | algebra | core_like, declaraciones despues del teorema: ['equal_chords_of_arc_midpoint'] |
| imo_2010_p5 | C | algebra |  |
| imo_2010_p6 | C | algebra |  |
| imo_2011_p1 | C | algebra |  |
| imo_2011_p2 | C | algebra | core_like |
| imo_2011_p3 | B | algebra |  |
| imo_2011_p4 | C | algebra |  |
| imo_2011_p5 | C | number_theory |  |
| imo_2011_p6 | C | algebra | core_like |
| imo_2012_p1 | C | algebra | core_like |
| imo_2012_p2 | C | algebra |  |
| imo_2012_p3 | C | algebra | core_like |
| imo_2012_p4 | C | algebra | core_like |
| imo_2012_p5 | C | algebra | core_like |
| imo_2013_p1 | C | algebra |  |
| imo_2013_p2 | C | algebra | core_like |
| imo_2013_p3 | C | geometry | core_like |
| imo_2013_p4 | C | algebra | core_like |
| imo_2014_p1 | C | algebra |  |
| imo_2014_p2 | C | algebra | core_like |
| imo_2014_p3 | C | algebra | core_like, declaraciones despues del teorema: ['angle_sum_rearrangement', 'angle_double_relation', 'final_right_angle'] |
| imo_2014_p4 | C | algebra | core_like |
| imo_2014_p5 | C | algebra | core_like, declaraciones despues del teorema: ['light_coin_fits_some_box'] |
| imo_2014_p6 | C | algebra | core_like |
| imo_2015_p1 | C | algebra | core_like, usa variable, declaraciones despues del teorema: ['two_coprime_of_odd'] |
| imo_2015_p2 | C | algebra | core_like |
| imo_2015_p3 | C | algebra | core_like, declaraciones despues del teorema: ['tangent_dot_product', 'equidistant_difference'] |
| imo_2015_p4 | C | algebra | core_like |
| imo_2015_p5 | C | algebra |  |
| imo_2015_p6 | C | algebra | core_like, declaraciones despues del teorema: ['midpoint_identity', 'final_square_identity'] |
| imo_2016_p1 | C | algebra | core_like |
| imo_2016_p2 | C | number_theory | core_like, declaraciones despues del teorema: ['three_dvd_of_nine_dvd', 'eq_nine_mul_of_nine_dvd'] |
| imo_2016_p3 | C | number_theory | core_like, declaraciones despues del teorema: ['three_dvd_of_nine_dvd', 'eq_nine_mul_of_nine_dvd'] |
| imo_2016_p4 | C | algebra | core_like, declaraciones despues del teorema: ['gap_one', 'gap_two', 'gap_three'] |
| imo_2016_p6 | C | algebra | core_like, declaraciones despues del teorema: ['even_iff_pred_odd', 'odd_n_of_alternating_arc'] |
| imo_2017_p1 | C | number_theory | core_like |
| imo_2017_p2 | C | algebra | usa variable |
| imo_2017_p3 | C | algebra | core_like |
| imo_2017_p4 | C | algebra | core_like |
| imo_2017_p6 | C | algebra |  |
| imo_2018_p1 | C | algebra | core_like |
| imo_2018_p2 | C | number_theory |  |
| imo_2018_p3 | C | algebra | core_like, declaraciones despues del teorema: ['numerical_core'] |
| imo_2018_p5 | C | number_theory | core_like |
| imo_2018_p6 | C | algebra | core_like |
| imo_2019_p1 | C | algebra |  |
| imo_2019_p2 | C | algebra | core_like, usa variable |
| imo_2019_p3 | C | algebra | core_like |
| imo_2019_p4 | C | algebra |  |
| imo_2019_p5 | C | algebra | core_like |
| imo_2019_p6 | C | algebra | core_like, usa variable |
| imo_2020_p1 | C | geometry | core_like, usa variable |
| imo_2020_p2 | C | algebra |  |
| imo_2020_p5 | C | algebra | core_like, usa variable |
| imo_2020_p6 | C | algebra | core_like, usa variable, declaraciones despues del teorema: ['clearance_of_hasSeparatingLine', 'min_positive_constant', 'two_case_separation'] |
| imo_2021_p1 | C | number_theory | core_like, declaraciones despues del teorema: ['source_square_identity_ab', 'source_square_identity_ac', 'source_square_identity_bc'] |
| imo_2021_p2 | C | algebra | declaraciones despues del teorema: ['two_abs_mul_le_sq_add_sq', 'neg_two_mul_le_sq_add_sq', 'two_mul_le_sq_add_sq'] |
| imo_2021_p3 | C | algebra | core_like, usa variable |
| imo_2021_p4 | C | geometry | core_like, usa variable |
| imo_2021_p5 | C | algebra | core_like |
| imo_2022_p1 | C | algebra | core_like, usa variable |
| imo_2022_p2 | C | algebra |  |
| imo_2022_p3 | C | geometry | core_like, usa variable |
| imo_2022_p6 | C | algebra | usa variable, declaraciones despues del teorema: ['edge_count_decomposition', 'edges_plus_singleton', 'minimum_eq_target'] |
| imo_2023_p1 | C | number_theory | core_like, declaraciones despues del teorema: ['prime_power_local_condition'] |
| imo_2023_p2 | C | geometry | core_like, usa variable |
| imo_2023_p3 | C | algebra | core_like |
| imo_2023_p4 | C | algebra | core_like |
| imo_2024_p1 | C | number_theory | core_like |
| imo_2024_p2 | C | number_theory | core_like |
| imo_2024_p4 | C | algebra | core_like, usa variable |
| imo_2024_p5 | C | algebra | usa variable, declaraciones despues del teorema: ['answer_is_three', 'minimum_positive_attempts_unique', 'positive_answer_is_three'] |
| imo_2025_p1 | C | algebra | core_like, usa variable |
| imo_2025_p4 | C | number_theory | core_like, usa variable, declaraciones despues del teorema: ['candidate_witness_form'] |
| imo_2025_p5 | C | algebra | usa variable, declaraciones despues del teorema: ['alice_iff_above', 'bazza_iff_below'] |
| imo_2026_p1 | C | algebra | core_like |
| imo_2026_p2 | C | algebra | core_like, usa variable |
| imo_2026_p3 | C | algebra | usa variable |
| imo_2026_p4 | C | algebra | usa variable, declaraciones despues del teorema: ['candidate_range', 'degrees_classification_step', 'descent_reaches_win'] |
| imo_2026_p5 | C | algebra |  |
| imo_2026_p6 | C | algebra | core_like, declaraciones despues del teorema: ['two_periods', 'iterate_period', 'add_period_strict_mono'] |
