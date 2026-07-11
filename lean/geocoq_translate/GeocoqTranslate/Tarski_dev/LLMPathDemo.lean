import GeocoqTranslate.Tarski_dev.SegmentCone

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

-- LLM PATH demo. v0 transliterator can't do these (case-splits / existentials).
-- Each was written from the orchestrator's scaffold (oracle structure +
-- port_map signatures + binder map), then passed the SAME verify gate.

-- (1) Bet_cases — case-split on a disjunction. Scaffold showed: left = hyp,
--     right = between_symmetry (port_map: implicit points dropped).
theorem Bet_cases_llm (A B C : Tpoint) (h : Bet A B C ∨ Bet C B A) : Bet A B C := by
  rcases h with h | h
  · exact h
  · exact between_symmetry h

-- (2) l3_17 — a real theorem: existential construction via two inner_pasch
--     applications. Scaffold gave the exact point mapping for inner_pasch and
--     the final between_exchange2 assembly.
theorem l3_17_llm (A B C A' B' P : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C) (h₃ : Bet A P A') :
    ∃ Q, Bet P Q C ∧ Bet B Q B' := by
  obtain ⟨x, _hB'xA, hPxC⟩ := inner_pasch C A A' B' P (between_symmetry h₂) h₃
  obtain ⟨y, hxyC, hByB'⟩ := inner_pasch B' C A x B _hB'xA (between_symmetry h₁)
  exact ⟨y, between_exchange2 hPxC hxyC, hByB'⟩

#print axioms GeocoqTranslate.Tarski.Base.Bet_cases_llm
#print axioms GeocoqTranslate.Tarski.Base.l3_17_llm

end GeocoqTranslate.Tarski.Base
