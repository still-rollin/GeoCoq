/- AUTO-GENERATED statement-faithfulness check.
   For each hand-translated lemma, assert the HAND proof inhabits the
   TRANSPILER-generated statement type. Compiles ⟺ statements are defeq. -/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_5b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6a
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7a
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_NCdistinct
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_TGsymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennesspreserved
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruenceflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_differenceofparts
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_doublereverse
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extensionunique
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_layoff
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_lessthancongruence
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_localextension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_partnotequalwhole
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_ray2
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_ray4
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_trichotomy2
namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

/-- lemma_3_5b -/
example : ∀ (A B C D : Point), BetS A B D → BetS B C D → BetS A C D := lemma_3_5b
/-- lemma_3_6a -/
example : ∀ (A B C D : Point), BetS A B C → BetS A C D → BetS B C D := lemma_3_6a
/-- lemma_3_6b -/
example : ∀ (A B C D : Point), BetS A B C → BetS A C D → BetS A B D := lemma_3_6b
/-- lemma_3_7a -/
example : ∀ (A B C D : Point), BetS A B C → BetS B C D → BetS A C D := lemma_3_7a
/-- lemma_3_7b -/
example : ∀ (A B C D : Point), BetS A B C → BetS B C D → BetS A B D := lemma_3_7b
/-- lemma_NCdistinct -/
example : ∀ (A B C : Point), nCol A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ B ≠ A ∧ C ≠ B ∧ C ≠ A := lemma_NCdistinct
/-- lemma_TGsymmetric -/
example : ∀ (A B C a b c : Point), TG A a B b C c → TG B b A a C c := lemma_TGsymmetric
/-- lemma_betweennesspreserved -/
example : ∀ (A B C a b c : Point), Cong A B a b → Cong A C a c → Cong B C b c → BetS A B C → BetS a b c := lemma_betweennesspreserved
/-- lemma_betweennotequal -/
example : ∀ (A B C : Point), BetS A B C → B ≠ C ∧ A ≠ B ∧ A ≠ C := lemma_betweennotequal
/-- lemma_congruenceflip -/
example : ∀ (A B C D : Point), Cong A B C D → Cong B A D C ∧ Cong B A C D ∧ Cong A B D C := lemma_congruenceflip
/-- lemma_congruencesymmetric -/
example : ∀ (A B C D : Point), Cong B C A D → Cong A D B C := lemma_congruencesymmetric
/-- lemma_congruencetransitive -/
example : ∀ (A B C D E F : Point), Cong A B C D → Cong C D E F → Cong A B E F := lemma_congruencetransitive
/-- lemma_differenceofparts -/
example : ∀ (A B C a b c : Point), Cong A B a b → Cong A C a c → BetS A B C → BetS a b c → Cong B C b c := lemma_differenceofparts
/-- lemma_doublereverse -/
example : ∀ (A B C D : Point), Cong A B C D → Cong D C B A ∧ Cong B A D C := lemma_doublereverse
/-- lemma_extension -/
example : ∀ (A B P Q : Point), A ≠ B → P ≠ Q → ∃ X, BetS A B X ∧ Cong B X P Q := lemma_extension
/-- lemma_extensionunique -/
example : ∀ (A B E F : Point), BetS A B E → BetS A B F → Cong B E B F → E = F := lemma_extensionunique
/-- lemma_inequalitysymmetric -/
example : ∀ (A B : Point), A ≠ B → B ≠ A := lemma_inequalitysymmetric
/-- lemma_layoff -/
example : ∀ (A B C D : Point), A ≠ B → C ≠ D → ∃ X, Out A B X ∧ Cong A X C D := lemma_layoff
/-- lemma_lessthancongruence -/
example : ∀ (A B C D E F : Point), Lt A B C D → Cong C D E F → Lt A B E F := lemma_lessthancongruence
/-- lemma_localextension -/
example : ∀ (A B Q : Point), A ≠ B → B ≠ Q → ∃ X, BetS A B X ∧ Cong B X B Q := lemma_localextension
/-- lemma_partnotequalwhole -/
example : ∀ (A B C : Point), BetS A B C → ¬ Cong A B A C := lemma_partnotequalwhole
/-- lemma_ray2 -/
example : ∀ (A B C : Point), Out A B C → A ≠ B := lemma_ray2
/-- lemma_ray4 -/
example : ∀ (A B E : Point), (BetS A E B ∨ E = B ∨ BetS A B E) → A ≠ B → Out A B E := lemma_ray4
/-- lemma_trichotomy2 -/
example : ∀ (A B C D : Point), Lt A B C D → ¬ Lt C D A B := lemma_trichotomy2

end GeocoqTranslate.Elements
