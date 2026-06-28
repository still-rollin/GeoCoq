# GeoCoq Project Checklist

Welcome to the GeoCoq project checklist! This document provides an exhaustive list of all the Coq (`.v`) files in the project.

## Project Statistics

Here are some interesting statistics about the GeoCoq codebase:

- **Total Coq Files**: 463
- **Total Lines of Code**: 162,167
- **Average File Size**: 350 lines
- **Largest File**: `theories/Main/Tarski_dev/Ch11_angles.v` (11,095 lines)

### Breakdown by Directory

| Directory | Files | Lines of Code | % of Total LOC |
|-----------|-------|---------------|----------------|
| **Main** | 165 | 118,246 | 72.9% |
| **Elements** | 239 | 22,118 | 13.6% |
| **Algebraic** | 37 | 12,746 | 7.9% |
| **Coinc** | 8 | 6,461 | 4.0% |
| **Axioms** | 14 | 2,596 | 1.6% |

---

## Interactive Checklist

Expand each section below to view the files and check them off as you progress.

<details>
<summary><strong>Algebraic (37 files, 12,746 lines)</strong></summary>

### Algebraic Component
This section bridges synthetic geometry with algebra. It focuses on algebraic counter-models (planar and n-dimensional spaces) and translations to algebraic frameworks. These are essential for proving independence of axioms or showing that certain properties do not hold in general spaces.

- [ ] `Counter_models/Planar/counter_model_bet_inner_transitivity.v` *(~116 lines)*
- [ ] `Counter_models/Planar/counter_model_bet_symmetry.v` *(~254 lines)*
- [ ] `Counter_models/Planar/counter_model_cong_identity.v` *(~146 lines)*
- [ ] `Counter_models/Planar/counter_model_cong_inner_transitivity.v` *(~147 lines)*
- [ ] `Counter_models/Planar/counter_model_cong_pseudo_reflexivity.v` *(~98 lines)*
- [ ] `Counter_models/Planar/counter_model_euclid.v` *(~310 lines)*
- [ ] `Counter_models/Planar/counter_model_five_segment.v` *(~439 lines)*
- [ ] `Counter_models/Planar/counter_model_lower_dim.v` *(~59 lines)*
- [ ] `Counter_models/Planar/counter_model_segment_construction.v` *(~59 lines)*
- [ ] `Counter_models/Planar/counter_model_upper_dim.v` *(~187 lines)*
- [ ] `Counter_models/Planar/gupta_inspired_to_independent_tarski.v` *(~58 lines)*
- [ ] `Counter_models/Planar/independence.v` *(~91 lines)*
- [ ] `Counter_models/Planar/independent_tarski_to_gupta_inspired.v` *(~68 lines)*
- [ ] `Counter_models/Planar/independent_version.v` *(~47 lines)*
- [ ] `Counter_models/counter_model_bet_identity.v` *(~192 lines)*
- [ ] `Counter_models/nD/bet_identity.v` *(~213 lines)*
- [ ] `Counter_models/nD/counter_model_bet_inner_transitivity.v` *(~310 lines)*
- [ ] `Counter_models/nD/counter_model_bet_symmetry.v` *(~174 lines)*
- [ ] `Counter_models/nD/counter_model_cong_identity.v` *(~65 lines)*
- [ ] `Counter_models/nD/counter_model_cong_inner_transitivity.v` *(~109 lines)*
- [ ] `Counter_models/nD/counter_model_cong_pseudo_reflexivity.v` *(~143 lines)*
- [ ] `Counter_models/nD/counter_model_euclid.v` *(~2947 lines)*
- [ ] `Counter_models/nD/counter_model_five_segment.v` *(~287 lines)*
- [ ] `Counter_models/nD/counter_model_lower_dim.v` *(~151 lines)*
- [ ] `Counter_models/nD/counter_model_segment_construction.v` *(~300 lines)*
- [ ] `Counter_models/nD/counter_model_upper_dim.v` *(~424 lines)*
- [ ] `Counter_models/nD/dimensional_axioms.v` *(~530 lines)*
- [ ] `Counter_models/nD/gupta_inspired_to_independent_version.v` *(~203 lines)*
- [ ] `Counter_models/nD/independence.v` *(~127 lines)*
- [ ] `Counter_models/nD/independent_version.v` *(~48 lines)*
- [ ] `Counter_models/nD/independent_version_to_beeson.v` *(~166 lines)*
- [ ] `Counter_models/nD/independent_version_to_tarski.v` *(~254 lines)*
- [ ] `Counter_models/nD/stability_properties.v` *(~77 lines)*
- [ ] `Counter_models/nD/stronger_pasch.v` *(~319 lines)*
- [ ] `POF_to_Tarski.v` *(~1515 lines)*
- [ ] `coplanarity.v` *(~369 lines)*
- [ ] `tcp_ndc.v` *(~1744 lines)*

</details>

<details>
<summary><strong>Axioms (14 files, 2,596 lines)</strong></summary>

### Axioms Component
This is the foundation of the GeoCoq library. It contains the formalization of various axiomatic systems for geometry, including Tarski's axioms, Hilbert's axioms, Beeson's axioms, and continuity axioms. Having these defined allows the library to establish meta-theorems and translations between different foundational frameworks.

- [ ] `Definitions.v` *(~602 lines)*
- [ ] `adg_definitions.v` *(~334 lines)*
- [ ] `beeson_s_axioms.v` *(~34 lines)*
- [ ] `continuity_axioms.v` *(~228 lines)*
- [ ] `euclidean_axioms.v` *(~190 lines)*
- [ ] `finish.v` *(~20 lines)*
- [ ] `gelertner_inspired_axioms.v` *(~484 lines)*
- [ ] `gupta_inspired_variant_axioms.v` *(~41 lines)*
- [ ] `hilbert_axioms.v` *(~165 lines)*
- [ ] `makarios_variant_axioms.v` *(~46 lines)*
- [ ] `parallel_postulates.v` *(~271 lines)*
- [ ] `playground.v` *(~36 lines)*
- [ ] `rocq_demo.v` *(~51 lines)*
- [ ] `tarski_axioms.v` *(~94 lines)*

</details>

<details>
<summary><strong>Coinc (8 files, 6,461 lines)</strong></summary>

### Coincidence Component
This section provides advanced tactics and permutation utilities specifically for incidence geometry (collinearity, coplanarity, conciclicity). It helps automate the often tedious proofs involving points that coincide or are collinear/coplanar.

- [ ] `CoincR.v` *(~1207 lines)*
- [ ] `ColR.v` *(~1501 lines)*
- [ ] `CongR.v` *(~600 lines)*
- [ ] `Permutations.v` *(~80 lines)*
- [ ] `Utils/arity.v` *(~1498 lines)*
- [ ] `Utils/general_tactics.v` *(~187 lines)*
- [ ] `Utils/sets.v` *(~1329 lines)*
- [ ] `tactics_axioms.v` *(~59 lines)*

</details>

<details>
<summary><strong>Elements (239 files, 22,118 lines)</strong></summary>

### Euclid's Elements
A major achievement of GeoCoq is the rigorous formalization of the original proofs from Euclid's *Elements* (Book 1, Book 3, etc.). This section contains the formalized propositions and the lemmas required to prove them, bridging classical Greek geometry with modern formal logic.

- [ ] `OriginalProofs/book1.v` *(~69 lines)*
- [ ] `OriginalProofs/euclidean_defs.v` *(~37 lines)*
- [ ] `OriginalProofs/euclidean_tactics.v` *(~141 lines)*
- [ ] `OriginalProofs/general_tactics.v` *(~44 lines)*
- [ ] `OriginalProofs/lemma_10_12.v` *(~83 lines)*
- [ ] `OriginalProofs/lemma_21helper.v` *(~56 lines)*
- [ ] `OriginalProofs/lemma_26helper.v` *(~88 lines)*
- [ ] `OriginalProofs/lemma_30helper.v` *(~93 lines)*
- [ ] `OriginalProofs/lemma_35helper.v` *(~207 lines)*
- [ ] `OriginalProofs/lemma_3_5b.v` *(~20 lines)*
- [ ] `OriginalProofs/lemma_3_6a.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_3_6b.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_3_7a.v` *(~26 lines)*
- [ ] `OriginalProofs/lemma_3_7b.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_8_2.v` *(~65 lines)*
- [ ] `OriginalProofs/lemma_8_3.v` *(~50 lines)*
- [ ] `OriginalProofs/lemma_8_7.v` *(~51 lines)*
- [ ] `OriginalProofs/lemma_9_5.v` *(~153 lines)*
- [ ] `OriginalProofs/lemma_9_5a.v` *(~103 lines)*
- [ ] `OriginalProofs/lemma_9_5b.v` *(~109 lines)*
- [ ] `OriginalProofs/lemma_ABCequalsCBA.v` *(~54 lines)*
- [ ] `OriginalProofs/lemma_EFreflexive.v` *(~49 lines)*
- [ ] `OriginalProofs/lemma_ETreflexive.v` *(~21 lines)*
- [ ] `OriginalProofs/lemma_Euclid4.v` *(~140 lines)*
- [ ] `OriginalProofs/lemma_NCdistinct.v` *(~39 lines)*
- [ ] `OriginalProofs/lemma_NChelper.v` *(~37 lines)*
- [ ] `OriginalProofs/lemma_NCorder.v` *(~48 lines)*
- [ ] `OriginalProofs/lemma_PGflip.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_PGrectangle.v` *(~62 lines)*
- [ ] `OriginalProofs/lemma_PGrotate.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_PGsymmetric.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_Pasch_outer2.v` *(~54 lines)*
- [ ] `OriginalProofs/lemma_Playfair.v` *(~49 lines)*
- [ ] `OriginalProofs/lemma_Playfairhelper.v` *(~86 lines)*
- [ ] `OriginalProofs/lemma_Playfairhelper2.v` *(~113 lines)*
- [ ] `OriginalProofs/lemma_RTcongruence.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_RTsymmetric.v` *(~30 lines)*
- [ ] `OriginalProofs/lemma_TCreflexive.v` *(~20 lines)*
- [ ] `OriginalProofs/lemma_TGflip.v` *(~38 lines)*
- [ ] `OriginalProofs/lemma_TGsymmetric.v` *(~35 lines)*
- [ ] `OriginalProofs/lemma_TTflip.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_TTflip2.v` *(~38 lines)*
- [ ] `OriginalProofs/lemma_TTorder.v` *(~20 lines)*
- [ ] `OriginalProofs/lemma_TTtransitive.v` *(~36 lines)*
- [ ] `OriginalProofs/lemma_altitudebisectsbase.v` *(~83 lines)*
- [ ] `OriginalProofs/lemma_altitudeofrighttriangle.v` *(~184 lines)*
- [ ] `OriginalProofs/lemma_angleaddition.v` *(~98 lines)*
- [ ] `OriginalProofs/lemma_angledistinct.v` *(~57 lines)*
- [ ] `OriginalProofs/lemma_angleorderrespectscongruence.v` *(~99 lines)*
- [ ] `OriginalProofs/lemma_angleorderrespectscongruence2.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_angleordertransitive.v` *(~89 lines)*
- [ ] `OriginalProofs/lemma_angletrichotomy.v` *(~161 lines)*
- [ ] `OriginalProofs/lemma_angletrichotomy2.v` *(~569 lines)*
- [ ] `OriginalProofs/lemma_betweennesspreserved.v` *(~40 lines)*
- [ ] `OriginalProofs/lemma_betweennotequal.v` *(~41 lines)*
- [ ] `OriginalProofs/lemma_collinear1.v` *(~49 lines)*
- [ ] `OriginalProofs/lemma_collinear2.v` *(~50 lines)*
- [ ] `OriginalProofs/lemma_collinear4.v` *(~195 lines)*
- [ ] `OriginalProofs/lemma_collinear5.v` *(~32 lines)*
- [ ] `OriginalProofs/lemma_collinearbetween.v` *(~169 lines)*
- [ ] `OriginalProofs/lemma_collinearitypreserved.v` *(~85 lines)*
- [ ] `OriginalProofs/lemma_collinearorder.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_collinearparallel.v` *(~37 lines)*
- [ ] `OriginalProofs/lemma_collinearparallel2.v` *(~64 lines)*
- [ ] `OriginalProofs/lemma_collinearright.v` *(~86 lines)*
- [ ] `OriginalProofs/lemma_congruenceflip.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_congruencesymmetric.v` *(~19 lines)*
- [ ] `OriginalProofs/lemma_congruencetransitive.v` *(~20 lines)*
- [ ] `OriginalProofs/lemma_crisscross.v` *(~218 lines)*
- [ ] `OriginalProofs/lemma_crossbar.v` *(~150 lines)*
- [ ] `OriginalProofs/lemma_crossbar2.v` *(~101 lines)*
- [ ] `OriginalProofs/lemma_crossimpliesopposite.v` *(~30 lines)*
- [ ] `OriginalProofs/lemma_diagonalsbisect.v` *(~128 lines)*
- [ ] `OriginalProofs/lemma_diagonalsmeet.v` *(~183 lines)*
- [ ] `OriginalProofs/lemma_differenceofparts.v` *(~72 lines)*
- [ ] `OriginalProofs/lemma_doublereverse.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_droppedperpendicularunique.v` *(~61 lines)*
- [ ] `OriginalProofs/lemma_equalanglesNC.v` *(~65 lines)*
- [ ] `OriginalProofs/lemma_equalanglesflip.v` *(~32 lines)*
- [ ] `OriginalProofs/lemma_equalangleshelper.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_equalanglesreflexive.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_equalanglessymmetric.v` *(~59 lines)*
- [ ] `OriginalProofs/lemma_equalanglestransitive.v` *(~62 lines)*
- [ ] `OriginalProofs/lemma_equalitysymmetric.v` *(~18 lines)*
- [ ] `OriginalProofs/lemma_equaltorightisright.v` *(~57 lines)*
- [ ] `OriginalProofs/lemma_erectedperpendicularunique.v` *(~43 lines)*
- [ ] `OriginalProofs/lemma_extension.v` *(~48 lines)*
- [ ] `OriginalProofs/lemma_extensionunique.v` *(~33 lines)*
- [ ] `OriginalProofs/lemma_fiveline.v` *(~68 lines)*
- [ ] `OriginalProofs/lemma_inequalitysymmetric.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_interior5.v` *(~57 lines)*
- [ ] `OriginalProofs/lemma_layoff.v` *(~32 lines)*
- [ ] `OriginalProofs/lemma_layoffunique.v` *(~138 lines)*
- [ ] `OriginalProofs/lemma_legsmallerhypotenuse.v` *(~87 lines)*
- [ ] `OriginalProofs/lemma_lessthanadditive.v` *(~92 lines)*
- [ ] `OriginalProofs/lemma_lessthanbetween.v` *(~27 lines)*
- [ ] `OriginalProofs/lemma_lessthancongruence.v` *(~61 lines)*
- [ ] `OriginalProofs/lemma_lessthancongruence2.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_lessthannotequal.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_lessthantransitive.v` *(~77 lines)*
- [ ] `OriginalProofs/lemma_linereflectionisometry.v` *(~165 lines)*
- [ ] `OriginalProofs/lemma_localextension.v` *(~28 lines)*
- [ ] `OriginalProofs/lemma_midpointunique.v` *(~70 lines)*
- [ ] `OriginalProofs/lemma_notperp.v` *(~156 lines)*
- [ ] `OriginalProofs/lemma_ondiameter.v` *(~52 lines)*
- [ ] `OriginalProofs/lemma_oppositesideflip.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_oppositesidesymmetric.v` *(~63 lines)*
- [ ] `OriginalProofs/lemma_outerconnectivity.v` *(~60 lines)*
- [ ] `OriginalProofs/lemma_parallelNC.v` *(~54 lines)*
- [ ] `OriginalProofs/lemma_parallelPasch.v` *(~65 lines)*
- [ ] `OriginalProofs/lemma_parallelbetween.v` *(~116 lines)*
- [ ] `OriginalProofs/lemma_parallelcollinear.v` *(~64 lines)*
- [ ] `OriginalProofs/lemma_parallelcollinear1.v` *(~280 lines)*
- [ ] `OriginalProofs/lemma_parallelcollinear2.v` *(~153 lines)*
- [ ] `OriginalProofs/lemma_paralleldef2A.v` *(~64 lines)*
- [ ] `OriginalProofs/lemma_paralleldef2B.v` *(~198 lines)*
- [ ] `OriginalProofs/lemma_parallelflip.v` *(~62 lines)*
- [ ] `OriginalProofs/lemma_parallelsymmetric.v` *(~29 lines)*
- [ ] `OriginalProofs/lemma_partnotequalwhole.v` *(~32 lines)*
- [ ] `OriginalProofs/lemma_paste5.v` *(~317 lines)*
- [ ] `OriginalProofs/lemma_planeseparation.v` *(~558 lines)*
- [ ] `OriginalProofs/lemma_pointreflectionisometry.v` *(~164 lines)*
- [ ] `OriginalProofs/lemma_ray.v` *(~46 lines)*
- [ ] `OriginalProofs/lemma_ray1.v` *(~27 lines)*
- [ ] `OriginalProofs/lemma_ray2.v` *(~21 lines)*
- [ ] `OriginalProofs/lemma_ray3.v` *(~47 lines)*
- [ ] `OriginalProofs/lemma_ray4.v` *(~45 lines)*
- [ ] `OriginalProofs/lemma_ray5.v` *(~23 lines)*
- [ ] `OriginalProofs/lemma_rayimpliescollinear.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_raystrict.v` *(~21 lines)*
- [ ] `OriginalProofs/lemma_rectangleparallelogram.v` *(~105 lines)*
- [ ] `OriginalProofs/lemma_rectanglereverse.v` *(~29 lines)*
- [ ] `OriginalProofs/lemma_rectanglerotate.v` *(~24 lines)*
- [ ] `OriginalProofs/lemma_rightangleNC.v` *(~139 lines)*
- [ ] `OriginalProofs/lemma_rightreverse.v` *(~26 lines)*
- [ ] `OriginalProofs/lemma_righttogether.v` *(~40 lines)*
- [ ] `OriginalProofs/lemma_samenotopposite.v` *(~29 lines)*
- [ ] `OriginalProofs/lemma_sameside2.v` *(~167 lines)*
- [ ] `OriginalProofs/lemma_samesidecollinear.v` *(~33 lines)*
- [ ] `OriginalProofs/lemma_samesideflip.v` *(~25 lines)*
- [ ] `OriginalProofs/lemma_samesidereflexive.v` *(~31 lines)*
- [ ] `OriginalProofs/lemma_samesidesymmetric.v` *(~27 lines)*
- [ ] `OriginalProofs/lemma_samesidetransitive.v` *(~25 lines)*
- [ ] `OriginalProofs/lemma_squareflip.v` *(~27 lines)*
- [ ] `OriginalProofs/lemma_squareparallelogram.v` *(~129 lines)*
- [ ] `OriginalProofs/lemma_squarerectangle.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_squaresequal.v` *(~74 lines)*
- [ ] `OriginalProofs/lemma_squareunique.v` *(~99 lines)*
- [ ] `OriginalProofs/lemma_subtractequals.v` *(~59 lines)*
- [ ] `OriginalProofs/lemma_supplementinequality.v` *(~146 lines)*
- [ ] `OriginalProofs/lemma_supplementofright.v` *(~25 lines)*
- [ ] `OriginalProofs/lemma_supplements.v` *(~140 lines)*
- [ ] `OriginalProofs/lemma_supplements2.v` *(~31 lines)*
- [ ] `OriginalProofs/lemma_supplementsymmetric.v` *(~22 lines)*
- [ ] `OriginalProofs/lemma_tarskiparallelflip.v` *(~60 lines)*
- [ ] `OriginalProofs/lemma_together.v` *(~36 lines)*
- [ ] `OriginalProofs/lemma_together2.v` *(~167 lines)*
- [ ] `OriginalProofs/lemma_trapezoiddiagonals.v` *(~57 lines)*
- [ ] `OriginalProofs/lemma_triangletoparallelogram.v` *(~96 lines)*
- [ ] `OriginalProofs/lemma_trichotomy1.v` *(~46 lines)*
- [ ] `OriginalProofs/lemma_trichotomy2.v` *(~33 lines)*
- [ ] `OriginalProofs/lemma_twolines.v` *(~55 lines)*
- [ ] `OriginalProofs/lemma_twolines2.v` *(~78 lines)*
- [ ] `OriginalProofs/lemma_twoperpsparallel.v` *(~41 lines)*
- [ ] `OriginalProofs/lemma_tworays.v` *(~65 lines)*
- [ ] `OriginalProofs/proposition_01.v` *(~86 lines)*
- [ ] `OriginalProofs/proposition_02.v` *(~56 lines)*
- [ ] `OriginalProofs/proposition_03.v` *(~22 lines)*
- [ ] `OriginalProofs/proposition_04.v` *(~230 lines)*
- [ ] `OriginalProofs/proposition_05.v` *(~30 lines)*
- [ ] `OriginalProofs/proposition_05b.v` *(~37 lines)*
- [ ] `OriginalProofs/proposition_06.v` *(~33 lines)*
- [ ] `OriginalProofs/proposition_06a.v` *(~84 lines)*
- [ ] `OriginalProofs/proposition_07.v` *(~305 lines)*
- [ ] `OriginalProofs/proposition_08.v` *(~108 lines)*
- [ ] `OriginalProofs/proposition_09.v` *(~88 lines)*
- [ ] `OriginalProofs/proposition_10.v` *(~167 lines)*
- [ ] `OriginalProofs/proposition_11.v` *(~40 lines)*
- [ ] `OriginalProofs/proposition_11B.v` *(~138 lines)*
- [ ] `OriginalProofs/proposition_12.v` *(~79 lines)*
- [ ] `OriginalProofs/proposition_13.v` *(~35 lines)*
- [ ] `OriginalProofs/proposition_14.v` *(~65 lines)*
- [ ] `OriginalProofs/proposition_15.v` *(~127 lines)*
- [ ] `OriginalProofs/proposition_16.v` *(~370 lines)*
- [ ] `OriginalProofs/proposition_17.v` *(~123 lines)*
- [ ] `OriginalProofs/proposition_18.v` *(~111 lines)*
- [ ] `OriginalProofs/proposition_19.v` *(~58 lines)*
- [ ] `OriginalProofs/proposition_20.v` *(~122 lines)*
- [ ] `OriginalProofs/proposition_21.v` *(~102 lines)*
- [ ] `OriginalProofs/proposition_22.v` *(~223 lines)*
- [ ] `OriginalProofs/proposition_23.v` *(~93 lines)*
- [ ] `OriginalProofs/proposition_23B.v` *(~289 lines)*
- [ ] `OriginalProofs/proposition_23C.v` *(~45 lines)*
- [ ] `OriginalProofs/proposition_24.v` *(~334 lines)*
- [ ] `OriginalProofs/proposition_25.v` *(~49 lines)*
- [ ] `OriginalProofs/proposition_26A.v` *(~126 lines)*
- [ ] `OriginalProofs/proposition_26B.v` *(~41 lines)*
- [ ] `OriginalProofs/proposition_27.v` *(~398 lines)*
- [ ] `OriginalProofs/proposition_27B.v` *(~42 lines)*
- [ ] `OriginalProofs/proposition_28A.v` *(~48 lines)*
- [ ] `OriginalProofs/proposition_28B.v` *(~47 lines)*
- [ ] `OriginalProofs/proposition_28C.v` *(~40 lines)*
- [ ] `OriginalProofs/proposition_28D.v` *(~43 lines)*
- [ ] `OriginalProofs/proposition_29.v` *(~243 lines)*
- [ ] `OriginalProofs/proposition_29B.v` *(~73 lines)*
- [ ] `OriginalProofs/proposition_29C.v` *(~92 lines)*
- [ ] `OriginalProofs/proposition_30.v` *(~305 lines)*
- [ ] `OriginalProofs/proposition_30A.v` *(~131 lines)*
- [ ] `OriginalProofs/proposition_30B.v` *(~82 lines)*
- [ ] `OriginalProofs/proposition_31.v` *(~187 lines)*
- [ ] `OriginalProofs/proposition_31short.v` *(~20 lines)*
- [ ] `OriginalProofs/proposition_32.v` *(~221 lines)*
- [ ] `OriginalProofs/proposition_33.v` *(~59 lines)*
- [ ] `OriginalProofs/proposition_33B.v` *(~38 lines)*
- [ ] `OriginalProofs/proposition_34.v` *(~100 lines)*
- [ ] `OriginalProofs/proposition_35.v` *(~480 lines)*
- [ ] `OriginalProofs/proposition_35A.v` *(~351 lines)*
- [ ] `OriginalProofs/proposition_36.v` *(~105 lines)*
- [ ] `OriginalProofs/proposition_36A.v` *(~57 lines)*
- [ ] `OriginalProofs/proposition_37.v` *(~78 lines)*
- [ ] `OriginalProofs/proposition_38.v` *(~75 lines)*
- [ ] `OriginalProofs/proposition_39.v` *(~115 lines)*
- [ ] `OriginalProofs/proposition_39A.v` *(~149 lines)*
- [ ] `OriginalProofs/proposition_40.v` *(~58 lines)*
- [ ] `OriginalProofs/proposition_41.v` *(~41 lines)*
- [ ] `OriginalProofs/proposition_42.v` *(~332 lines)*
- [ ] `OriginalProofs/proposition_42B.v` *(~125 lines)*
- [ ] `OriginalProofs/proposition_43.v` *(~50 lines)*
- [ ] `OriginalProofs/proposition_43B.v` *(~153 lines)*
- [ ] `OriginalProofs/proposition_44.v` *(~82 lines)*
- [ ] `OriginalProofs/proposition_44A.v` *(~264 lines)*
- [ ] `OriginalProofs/proposition_45.v` *(~183 lines)*
- [ ] `OriginalProofs/proposition_46.v` *(~201 lines)*
- [ ] `OriginalProofs/proposition_47.v` *(~79 lines)*
- [ ] `OriginalProofs/proposition_47A.v` *(~234 lines)*
- [ ] `OriginalProofs/proposition_47B.v` *(~216 lines)*
- [ ] `OriginalProofs/proposition_48.v` *(~89 lines)*
- [ ] `OriginalProofs/proposition_48A.v` *(~117 lines)*
- [ ] `euclid_to_tarski.v` *(~284 lines)*

</details>

<details>
<summary><strong>Main (165 files, 118,246 lines)</strong></summary>

### Main Meta-theory and High-School Geometry
The largest section of the project. It includes:
- **Tarski_dev**: Development of Tarski's geometry chapters.
- **Meta_theory**: Models, parallel postulates, and continuity.
- **Highschool**: Formalization of standard high-school geometry theorems (e.g., Euler line, Orthocenter, Varignon's theorem).
- **Annexes**: Additional theorems about circles, quadrilaterals, tangency, etc.

- [ ] `Annexes/Tagged_predicates.v` *(~160 lines)*
- [ ] `Annexes/circles.v` *(~2035 lines)*
- [ ] `Annexes/coplanar.v` *(~599 lines)*
- [ ] `Annexes/defect.v` *(~370 lines)*
- [ ] `Annexes/half_angles.v` *(~632 lines)*
- [ ] `Annexes/inscribed_angle.v` *(~809 lines)*
- [ ] `Annexes/midpoint_theorems.v` *(~354 lines)*
- [ ] `Annexes/perp_bisect.v` *(~296 lines)*
- [ ] `Annexes/project.v` *(~2415 lines)*
- [ ] `Annexes/quadrilaterals.v` *(~2799 lines)*
- [ ] `Annexes/quadrilaterals_inter_dec.v` *(~4800 lines)*
- [ ] `Annexes/rhombus.v` *(~267 lines)*
- [ ] `Annexes/saccheri.v` *(~2378 lines)*
- [ ] `Annexes/suma.v` *(~2490 lines)*
- [ ] `Annexes/sums.v` *(~384 lines)*
- [ ] `Annexes/tangency.v` *(~923 lines)*
- [ ] `Annexes/vectors.v` *(~2777 lines)*
- [ ] `Elements_statements/Book_1.v` *(~919 lines)*
- [ ] `Elements_statements/Book_3.v` *(~150 lines)*
- [ ] `Highschool/Euler_line.v` *(~374 lines)*
- [ ] `Highschool/SegmTrisect.v` *(~714 lines)*
- [ ] `Highschool/bisector.v` *(~420 lines)*
- [ ] `Highschool/circumcenter.v` *(~761 lines)*
- [ ] `Highschool/concyclic.v` *(~239 lines)*
- [ ] `Highschool/exercises.v` *(~118 lines)*
- [ ] `Highschool/gravityCenter.v` *(~591 lines)*
- [ ] `Highschool/incenter.v` *(~162 lines)*
- [ ] `Highschool/midpoint_thales.v` *(~86 lines)*
- [ ] `Highschool/orientation.v` *(~4788 lines)*
- [ ] `Highschool/orthocenter.v` *(~329 lines)*
- [ ] `Highschool/sesamath_exercises.v` *(~643 lines)*
- [ ] `Highschool/triangles.v` *(~346 lines)*
- [ ] `Highschool/varignon.v` *(~240 lines)*
- [ ] `Meta_theory/Continuity/angle_archimedes.v` *(~486 lines)*
- [ ] `Meta_theory/Continuity/archimedes.v` *(~396 lines)*
- [ ] `Meta_theory/Continuity/archimedes_cantor_dedekind.v` *(~140 lines)*
- [ ] `Meta_theory/Continuity/aristotle.v` *(~351 lines)*
- [ ] `Meta_theory/Continuity/cantor_completeness.v` *(~19 lines)*
- [ ] `Meta_theory/Continuity/cantor_variant.v` *(~54 lines)*
- [ ] `Meta_theory/Continuity/completeness.v` *(~368 lines)*
- [ ] `Meta_theory/Continuity/dedekind_archimedes.v` *(~207 lines)*
- [ ] `Meta_theory/Continuity/dedekind_cantor.v` *(~128 lines)*
- [ ] `Meta_theory/Continuity/dedekind_completeness.v` *(~265 lines)*
- [ ] `Meta_theory/Continuity/dedekind_variant.v` *(~70 lines)*
- [ ] `Meta_theory/Continuity/elementary_continuity_props.v` *(~413 lines)*
- [ ] `Meta_theory/Continuity/first_order.v` *(~73 lines)*
- [ ] `Meta_theory/Continuity/first_order_dedekind_circle_circle.v` *(~364 lines)*
- [ ] `Meta_theory/Continuity/grad.v` *(~288 lines)*
- [ ] `Meta_theory/Decidability/equivalence_between_decidability_properties_of_basic_relations.v` *(~69 lines)*
- [ ] `Meta_theory/Dimension_axioms/upper_dim_2.v` *(~344 lines)*
- [ ] `Meta_theory/Dimension_axioms/upper_dim_3.v` *(~292 lines)*
- [ ] `Meta_theory/Models/beeson_to_tarski.v` *(~245 lines)*
- [ ] `Meta_theory/Models/gupta_inspired_to_tarski.v` *(~421 lines)*
- [ ] `Meta_theory/Models/hilbert_to_tarski.v` *(~5854 lines)*
- [ ] `Meta_theory/Models/makarios_to_tarski.v` *(~126 lines)*
- [ ] `Meta_theory/Models/tarski_continuous_to_trc.v` *(~19 lines)*
- [ ] `Meta_theory/Models/tarski_to_beeson.v` *(~346 lines)*
- [ ] `Meta_theory/Models/tarski_to_coinc_theory_for_col.v` *(~82 lines)*
- [ ] `Meta_theory/Models/tarski_to_coinc_theory_for_concyclic.v` *(~67 lines)*
- [ ] `Meta_theory/Models/tarski_to_coinc_theory_for_cop.v` *(~82 lines)*
- [ ] `Meta_theory/Models/tarski_to_col_theory.v` *(~15 lines)*
- [ ] `Meta_theory/Models/tarski_to_cong_theory.v` *(~15 lines)*
- [ ] `Meta_theory/Models/tarski_to_euclid.v` *(~766 lines)*
- [ ] `Meta_theory/Models/tarski_to_gupta_inspired.v` *(~55 lines)*
- [ ] `Meta_theory/Models/tarski_to_hilbert.v` *(~1317 lines)*
- [ ] `Meta_theory/Models/tarski_to_makarios.v` *(~89 lines)*
- [ ] `Meta_theory/Parallel_postulates/SPP_ID.v` *(~60 lines)*
- [ ] `Meta_theory/Parallel_postulates/SPP_tarski.v` *(~287 lines)*
- [ ] `Meta_theory/Parallel_postulates/TCP_tarski.v` *(~436 lines)*
- [ ] `Meta_theory/Parallel_postulates/alternate_interior_angles_consecutive_interior_angles.v` *(~26 lines)*
- [ ] `Meta_theory/Parallel_postulates/alternate_interior_angles_playfair_bis.v` *(~80 lines)*
- [ ] `Meta_theory/Parallel_postulates/alternate_interior_angles_proclus.v` *(~120 lines)*
- [ ] `Meta_theory/Parallel_postulates/alternate_interior_angles_triangle.v` *(~41 lines)*
- [ ] `Meta_theory/Parallel_postulates/bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.v` *(~247 lines)*
- [ ] `Meta_theory/Parallel_postulates/bachmann_s_lotschnittaxiom_variant.v` *(~66 lines)*
- [ ] `Meta_theory/Parallel_postulates/bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.v` *(~82 lines)*
- [ ] `Meta_theory/Parallel_postulates/bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.v` *(~36 lines)*
- [ ] `Meta_theory/Parallel_postulates/consecutive_interior_angles_alternate_interior_angles.v` *(~26 lines)*
- [ ] `Meta_theory/Parallel_postulates/euclid_5_original_euclid.v` *(~76 lines)*
- [ ] `Meta_theory/Parallel_postulates/existential_playfair_rah.v` *(~70 lines)*
- [ ] `Meta_theory/Parallel_postulates/existential_saccheri_rah.v` *(~15 lines)*
- [ ] `Meta_theory/Parallel_postulates/existential_triangle_rah.v` *(~16 lines)*
- [ ] `Meta_theory/Parallel_postulates/inverse_projection_postulate_proclus_bis.v` *(~82 lines)*
- [ ] `Meta_theory/Parallel_postulates/legendre.v` *(~295 lines)*
- [ ] `Meta_theory/Parallel_postulates/midpoint_playfair.v` *(~90 lines)*
- [ ] `Meta_theory/Parallel_postulates/original_euclid_original_spp.v` *(~54 lines)*
- [ ] `Meta_theory/Parallel_postulates/original_spp_inverse_projection_postulate.v` *(~100 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_perp_2_par_par_perp_perp.v` *(~44 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_perp_perp_TCP.v` *(~84 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_perp_perp_par_perp_2_par.v` *(~18 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_perp_perp_playfair.v` *(~70 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_trans_NID.v` *(~315 lines)*
- [ ] `Meta_theory/Parallel_postulates/par_trans_playfair.v` *(~18 lines)*
- [ ] `Meta_theory/Parallel_postulates/parallel_postulates.v` *(~744 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_alternate_interior_angles.v` *(~25 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_bis_playfair.v` *(~54 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_existential_playfair.v` *(~17 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_midpoint.v` *(~31 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_par_trans.v` *(~61 lines)*
- [ ] `Meta_theory/Parallel_postulates/playfair_universal_posidonius_postulate.v` *(~76 lines)*
- [ ] `Meta_theory/Parallel_postulates/posidonius_postulate_rah.v` *(~124 lines)*
- [ ] `Meta_theory/Parallel_postulates/proclus_SPP.v` *(~20 lines)*
- [ ] `Meta_theory/Parallel_postulates/proclus_aristotle.v` *(~135 lines)*
- [ ] `Meta_theory/Parallel_postulates/proclus_bis_proclus.v` *(~64 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_existential_saccheri.v` *(~18 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_posidonius_postulate.v` *(~85 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_rectangle_principle.v` *(~14 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_similar.v` *(~56 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_thales_postulate.v` *(~22 lines)*
- [ ] `Meta_theory/Parallel_postulates/rah_triangle.v` *(~14 lines)*
- [ ] `Meta_theory/Parallel_postulates/rectangle_existence_rah.v` *(~15 lines)*
- [ ] `Meta_theory/Parallel_postulates/rectangle_principle_rectangle_existence.v` *(~21 lines)*
- [ ] `Meta_theory/Parallel_postulates/similar_rah.v` *(~159 lines)*
- [ ] `Meta_theory/Parallel_postulates/szmielew.v` *(~67 lines)*
- [ ] `Meta_theory/Parallel_postulates/tarski_euclid.v` *(~170 lines)*
- [ ] `Meta_theory/Parallel_postulates/tarski_playfair.v` *(~120 lines)*
- [ ] `Meta_theory/Parallel_postulates/tarski_s_euclid_remove_degenerated_cases.v` *(~104 lines)*
- [ ] `Meta_theory/Parallel_postulates/thales_converse_postulate_thales_existence.v` *(~22 lines)*
- [ ] `Meta_theory/Parallel_postulates/thales_converse_postulate_weak_triangle_circumscription_principle.v` *(~20 lines)*
- [ ] `Meta_theory/Parallel_postulates/thales_existence_rah.v` *(~17 lines)*
- [ ] `Meta_theory/Parallel_postulates/thales_postulate_thales_converse_postulate.v` *(~49 lines)*
- [ ] `Meta_theory/Parallel_postulates/triangle_existential_triangle.v` *(~22 lines)*
- [ ] `Meta_theory/Parallel_postulates/triangle_playfair_bis.v` *(~189 lines)*
- [ ] `Meta_theory/Parallel_postulates/universal_posidonius_postulate_par_perp_perp.v` *(~133 lines)*
- [ ] `Meta_theory/Parallel_postulates/weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.v` *(~126 lines)*
- [ ] `Meta_theory/Parallel_postulates/weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.v` *(~97 lines)*
- [ ] `Meta_theory/Parallel_postulates/weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.v` *(~150 lines)*
- [ ] `Meta_theory/Parallel_postulates/weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.v` *(~37 lines)*
- [ ] `Tactics/CoincR_for_col.v` *(~151 lines)*
- [ ] `Tactics/CoincR_for_concy.v` *(~163 lines)*
- [ ] `Tactics/CoincR_for_cop.v` *(~163 lines)*
- [ ] `Tactics/ColR.v` *(~220 lines)*
- [ ] `Tactics/CongR.v` *(~99 lines)*
- [ ] `Tarski_dev/Ch02_cong.v` *(~327 lines)*
- [ ] `Tarski_dev/Ch03_bet.v` *(~389 lines)*
- [ ] `Tarski_dev/Ch04_col.v` *(~273 lines)*
- [ ] `Tarski_dev/Ch04_cong_bet.v` *(~127 lines)*
- [ ] `Tarski_dev/Ch05_bet_le.v` *(~881 lines)*
- [ ] `Tarski_dev/Ch06_out_lines.v` *(~1022 lines)*
- [ ] `Tarski_dev/Ch07_midpoint.v` *(~1529 lines)*
- [ ] `Tarski_dev/Ch08_orthogonality.v` *(~2801 lines)*
- [ ] `Tarski_dev/Ch09_plane.v` *(~3900 lines)*
- [ ] `Tarski_dev/Ch10_line_reflexivity.v` *(~1761 lines)*
- [ ] `Tarski_dev/Ch10_line_reflexivity_2.v` *(~974 lines)*
- [ ] `Tarski_dev/Ch11_angles.v` *(~11095 lines)*
- [ ] `Tarski_dev/Ch12_parallel.v` *(~2336 lines)*
- [ ] `Tarski_dev/Ch12_parallel_inter_dec.v` *(~617 lines)*
- [ ] `Tarski_dev/Ch13_1.v` *(~4338 lines)*
- [ ] `Tarski_dev/Ch13_2_length.v` *(~537 lines)*
- [ ] `Tarski_dev/Ch13_3_angles.v` *(~1357 lines)*
- [ ] `Tarski_dev/Ch13_4_cos.v` *(~1998 lines)*
- [ ] `Tarski_dev/Ch13_5_Pappus_Pascal.v` *(~1805 lines)*
- [ ] `Tarski_dev/Ch13_6_Desargues_Hessenberg.v` *(~2182 lines)*
- [ ] `Tarski_dev/Ch14_order.v` *(~1932 lines)*
- [ ] `Tarski_dev/Ch14_prod.v` *(~3285 lines)*
- [ ] `Tarski_dev/Ch14_sum.v` *(~4587 lines)*
- [ ] `Tarski_dev/Ch15_lengths.v` *(~5494 lines)*
- [ ] `Tarski_dev/Ch15_pyth_rel.v` *(~1095 lines)*
- [ ] `Tarski_dev/Ch16_coordinates.v` *(~2487 lines)*
- [ ] `Tarski_dev/Ch16_coordinates_with_functions.v` *(~2233 lines)*
- [ ] `Unit_Tests/unit_tests.v` *(~489 lines)*
- [ ] `Unit_Tests/unit_tests_2.v` *(~203 lines)*
- [ ] `Utils/all_equiv.v` *(~253 lines)*
- [ ] `Utils/triples.v` *(~7 lines)*
- [ ] `main.v` *(~10 lines)*

</details>

